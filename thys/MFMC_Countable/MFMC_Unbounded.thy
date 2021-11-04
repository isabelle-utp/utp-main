(* Author: Andreas Lochbihler, ETH Zurich *)

section \<open>The max-flow min-cut theorems in unbounded networks\<close>

theory MFMC_Unbounded imports
  MFMC_Web
  MFMC_Flow_Attainability
  MFMC_Reduction
begin

subsection \<open>More about waves\<close>

lemma SINK_plus_current: "SINK (plus_current f g) = SINK f \<inter> SINK g"
by(auto simp add: SINK.simps set_eq_iff d_OUT_def nn_integral_0_iff emeasure_count_space_eq_0 add_eq_0_iff_both_eq_0)

abbreviation plus_web :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> 'v current \<Rightarrow> 'v current" ("_ \<frown>\<index> _" [66, 66] 65)
where "plus_web \<Gamma> f g \<equiv> plus_current f (g \<upharpoonleft> \<Gamma> / f)"

lemma d_OUT_plus_web:
  fixes \<Gamma> (structure)
  shows "d_OUT (f \<frown> g) x = d_OUT f x + d_OUT (g \<upharpoonleft> \<Gamma> / f) x" (is "?lhs = ?rhs")
proof -
  have "?lhs = d_OUT f x + (\<Sum>\<^sup>+ y. (if x \<in> RF\<^sup>\<circ> (TER f) then 0 else g (x, y) * indicator (- RF (TER f)) y))"
    unfolding d_OUT_def by(subst nn_integral_add[symmetric])(auto intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = ?rhs" by(auto simp add: d_OUT_def intro!: arg_cong2[where f="(+)"] nn_integral_cong)
  finally show "?thesis" .
qed

lemma d_IN_plus_web:
  fixes \<Gamma> (structure)
  shows "d_IN (f \<frown> g) y = d_IN f y + d_IN (g \<upharpoonleft> \<Gamma> / f) y" (is "?lhs = ?rhs")
proof -
  have "?lhs = d_IN f y + (\<Sum>\<^sup>+ x. (if y \<in> RF (TER f) then 0 else g (x, y) * indicator (- RF\<^sup>\<circ> (TER f)) x))"
    unfolding d_IN_def by(subst nn_integral_add[symmetric])(auto intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = ?rhs" by(auto simp add: d_IN_def intro!: arg_cong2[where f="(+)"] nn_integral_cong)
  finally show ?thesis .
qed

lemma plus_web_greater: "f e \<le> (f \<frown>\<^bsub>\<Gamma>\<^esub> g) e"
by(cases e)(auto split: split_indicator)

lemma current_plus_web:
  fixes \<Gamma> (structure)
  shows "\<lbrakk> current \<Gamma> f; wave \<Gamma> f; current \<Gamma> g \<rbrakk> \<Longrightarrow> current \<Gamma> (f \<frown> g)"
by(blast intro: current_plus_current current_restrict_current)

context
  fixes \<Gamma> :: "('v, 'more) web_scheme" (structure)
  and f g :: "'v current"
  assumes f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  and g: "current \<Gamma> g"
begin

context
  fixes x :: "'v"
  assumes x: "x \<in> \<E> (TER f \<union> TER g)"
begin

qualified lemma RF_f: "x \<notin> RF\<^sup>\<circ> (TER f)"
proof
  assume *: "x \<in> RF\<^sup>\<circ> (TER f)"

  from x obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
    and bypass: "\<And>z. \<lbrakk>x \<noteq> y; z \<in> set p\<rbrakk> \<Longrightarrow> z = x \<or> z \<notin> TER f \<union> TER g" by(rule \<E>_E) blast
  from rtrancl_path_distinct[OF p] obtain p'
    where p: "path \<Gamma> x p' y" and p': "set p' \<subseteq> set p" and distinct: "distinct (x # p')" .

  from * have x': "x \<in> RF (TER f)" and \<E>: "x \<notin> \<E> (TER f)" by(auto simp add: roofed_circ_def)
  hence "x \<notin> TER f" using not_essentialD[OF _ p y] p' bypass by blast
  with roofedD[OF x' p y] obtain z where z: "z \<in> set p'" "z \<in> TER f" by auto
  with p have "y \<in> set p'" by(auto dest!: rtrancl_path_last intro: last_in_set)
  with distinct have "x \<noteq> y" by auto
  with bypass z p' distinct show False by auto
qed

private lemma RF_g: "x \<notin> RF\<^sup>\<circ> (TER g)"
proof
  assume *: "x \<in> RF\<^sup>\<circ> (TER g)"

  from x obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
    and bypass: "\<And>z. \<lbrakk>x \<noteq> y; z \<in> set p\<rbrakk> \<Longrightarrow> z = x \<or> z \<notin> TER f \<union> TER g" by(rule \<E>_E) blast
  from rtrancl_path_distinct[OF p] obtain p'
    where p: "path \<Gamma> x p' y" and p': "set p' \<subseteq> set p" and distinct: "distinct (x # p')" .

  from * have x': "x \<in> RF (TER g)" and \<E>: "x \<notin> \<E> (TER g)" by(auto simp add: roofed_circ_def)
  hence "x \<notin> TER g" using not_essentialD[OF _ p y] p' bypass by blast
  with roofedD[OF x' p y] obtain z where z: "z \<in> set p'" "z \<in> TER g" by auto
  with p have "y \<in> set p'" by(auto dest!: rtrancl_path_last intro: last_in_set)
  with distinct have "x \<noteq> y" by auto
  with bypass z p' distinct show False by auto
qed

lemma TER_plus_web_aux:
  assumes SINK: "x \<in> SINK (g \<upharpoonleft> \<Gamma> / f)" (is "_ \<in> SINK ?g")
  shows "x \<in> TER (f \<frown> g)"
proof
  from x obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
    and bypass: "\<And>z. \<lbrakk>x \<noteq> y; z \<in> set p\<rbrakk> \<Longrightarrow> z = x \<or> z \<notin> TER f \<union> TER g" by(rule \<E>_E) blast
  from rtrancl_path_distinct[OF p] obtain p'
    where p: "path \<Gamma> x p' y" and p': "set p' \<subseteq> set p" and distinct: "distinct (x # p')" .

  from RF_f have "x \<in> SINK f"
    by(auto simp add: roofed_circ_def SINK.simps dest: waveD_OUT[OF w])
  thus "x \<in> SINK (f \<frown> g)" using SINK
    by(simp add: SINK.simps d_OUT_plus_web)
  show "x \<in> SAT \<Gamma> (f \<frown> g)"
  proof(cases "x \<in> TER f")
    case True
    hence "x \<in> SAT \<Gamma> f" by simp
    moreover have "\<dots> \<subseteq> SAT \<Gamma> (f \<frown> g)" by(rule SAT_mono plus_web_greater)+
    ultimately show ?thesis by blast
  next
    case False
    with x have "x \<in> TER g" by auto
    from False RF_f have "x \<notin> RF (TER f)" by(auto simp add: roofed_circ_def)
    moreover { fix z
      assume z: "z \<in> RF\<^sup>\<circ> (TER f)"
      have "(z, x) \<notin> \<^bold>E"
      proof
        assume "(z, x) \<in> \<^bold>E"
        hence path': "path \<Gamma> z (x # p') y" using p by(simp add: rtrancl_path.step)
        from z have "z \<in> RF (TER f)" by(simp add: roofed_circ_def)
        from roofedD[OF this path' y] False
        consider (path) z' where  "z' \<in> set p'" "z' \<in> TER f" | (TER) "z \<in> TER f" by auto
        then show False
        proof cases
          { case (path z')
            with p distinct have "x \<noteq> y"
              by(auto 4 3 intro: last_in_set elim: rtrancl_path.cases dest: rtrancl_path_last[symmetric])
            from bypass[OF this, of z'] path False p' show False by auto }
          note that = this
          case TER
          with z have "\<not> essential \<Gamma> (B \<Gamma>) (TER f) z" by(simp add: roofed_circ_def)
          from not_essentialD[OF this path' y] False obtain z' where "z' \<in> set p'" "z' \<in> TER f" by auto
          thus False by(rule that)
        qed
      qed }
    ultimately have "d_IN ?g x = d_IN g x" unfolding d_IN_def
      by(intro nn_integral_cong)(clarsimp split: split_indicator simp add: currentD_outside[OF g])
    hence "d_IN (f \<frown> g) x \<ge> d_IN g x"
      by(simp add: d_IN_plus_web)
    with \<open>x \<in> TER g\<close> show ?thesis by(auto elim!: SAT.cases intro: SAT.intros)
  qed
qed

qualified lemma SINK_TER_in'':
  assumes "\<And>x. x \<notin> RF (TER g) \<Longrightarrow> d_OUT g x = 0"
  shows "x \<in> SINK g"
using RF_g by(auto simp add: roofed_circ_def SINK.simps assms)

end

lemma wave_plus: "wave (quotient_web \<Gamma> f) (g \<upharpoonleft> \<Gamma> / f) \<Longrightarrow> wave \<Gamma> (f \<frown> g)"
using f w by(rule wave_plus_current)(rule current_restrict_current[OF w g])

lemma TER_plus_web'':
  assumes "\<And>x. x \<notin> RF (TER g) \<Longrightarrow> d_OUT g x = 0"
  shows "\<E> (TER f \<union> TER g) \<subseteq> TER (f \<frown> g)"
proof
  fix x
  assume *: "x \<in> \<E> (TER f \<union> TER g)"
  moreover have "x \<in> SINK (g \<upharpoonleft> \<Gamma> / f)"
    by(rule in_SINK_restrict_current)(rule MFMC_Unbounded.SINK_TER_in''[OF f w g * assms])
  ultimately show "x \<in> TER (f \<frown> g)" by(rule TER_plus_web_aux)
qed

lemma TER_plus_web': "wave \<Gamma> g \<Longrightarrow> \<E> (TER f \<union> TER g) \<subseteq> TER (f \<frown> g)"
by(rule TER_plus_web'')(rule waveD_OUT)

lemma wave_plus': "wave \<Gamma> g \<Longrightarrow> wave \<Gamma> (f \<frown> g)"
by(rule wave_plus)(rule wave_restrict_current[OF f w g])

end

lemma RF_TER_plus_web:
  fixes \<Gamma> (structure)
  assumes f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  and g: "current \<Gamma> g"
  and w': "wave \<Gamma> g"
  shows "RF (TER (f \<frown> g)) = RF (TER f \<union> TER g)"
proof
  have "RF (\<E> (TER f \<union> TER g)) \<subseteq> RF (TER (f \<frown> g))"
    by(rule roofed_mono)(rule TER_plus_web'[OF f w g w'])
  also have "RF (\<E> (TER f \<union> TER g)) = RF (TER f \<union> TER g)" by(rule RF_essential)
  finally show "\<dots> \<subseteq> RF (TER (f \<frown> g))" .
next
  have fg: "current \<Gamma> (f \<frown> g)" using f w g by(rule current_plus_web)
  show "RF (TER (f \<frown> g)) \<subseteq> RF (TER f \<union> TER g)"
  proof(intro subsetI roofedI)
    fix x p y
    assume RF: "x \<in> RF (TER (f \<frown> g))" and p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
    from roofedD[OF RF p y] obtain z where z: "z \<in> set (x # p)" and TER: "z \<in> TER (f \<frown> g)" by auto
    from TER have SINK: "z \<in> SINK f"
      by(auto simp add: SINK.simps d_OUT_plus_web add_eq_0_iff_both_eq_0)
    from TER have "z \<in> SAT \<Gamma> (f \<frown> g)" by simp
    hence SAT: "z \<in> SAT \<Gamma> f \<union> SAT \<Gamma> g"
      by(cases "z \<in> RF (TER f)")(auto simp add: currentD_SAT[OF f] currentD_SAT[OF g] currentD_SAT[OF fg] d_IN_plus_web d_IN_restrict_current_outside restrict_current_IN_not_RF[OF g] wave_not_RF_IN_zero[OF f w])

    show "(\<exists>z\<in>set p. z \<in> TER f \<union> TER g) \<or> x \<in> TER f \<union> TER g"
    proof(cases "z \<in> RF (TER g)")
      case False
      hence "z \<in> SINK g" by(simp add: SINK.simps waveD_OUT[OF w'])
      with SINK SAT have "z \<in> TER f \<union> TER g" by auto
      thus ?thesis using z by auto
    next
      case True
      from split_list[OF z] obtain ys zs where split: "x # p = ys @ z # zs" by blast
      with p have "path \<Gamma> z zs y" by(auto elim: rtrancl_path_appendE simp add: Cons_eq_append_conv)
      from roofedD[OF True this y] split show ?thesis by(auto simp add: Cons_eq_append_conv)
    qed
  qed
qed

lemma RF_TER_Sup:
  fixes \<Gamma> (structure)
  assumes f: "\<And>f. f \<in> Y \<Longrightarrow> current \<Gamma> f"
  and w: "\<And>f. f \<in> Y \<Longrightarrow> wave \<Gamma> f"
  and Y: "Complete_Partial_Order.chain (\<le>) Y" "Y \<noteq> {}" "countable (support_flow (Sup Y))"
  shows "RF (TER (Sup Y)) = RF (\<Union>f\<in>Y. TER f)"
proof(rule set_eqI iffI)+
  fix x
  assume x: "x \<in> RF (TER (Sup Y))"
  have "x \<in> RF (RF (\<Union>f\<in>Y. TER f))"
  proof
    fix p y
    assume p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
    from roofedD[OF x p y] obtain z where z: "z \<in> set (x # p)" and TER: "z \<in> TER (Sup Y)" by auto
    from TER have SINK: "z \<in> SINK f" if "f \<in> Y" for f using that by(auto simp add: SINK_Sup[OF Y])

    from Y(2) obtain f where y: "f \<in> Y" by blast

    show "(\<exists>z\<in>set p. z \<in> RF (\<Union>f\<in>Y. TER f)) \<or> x \<in> RF (\<Union>f\<in>Y. TER f)"
    proof(cases "\<exists>f\<in>Y. z \<in> RF (TER f)")
      case True
      then obtain f where fY: "f \<in> Y" and zf: "z \<in> RF (TER f)" by blast
      from zf have "z \<in> RF (\<Union>f\<in>Y. TER f)" by(rule in_roofed_mono)(auto intro: fY)
      with z show ?thesis by auto
    next
      case False
      hence *: "d_IN f z = 0" if "f \<in> Y" for f using that by(auto intro: wave_not_RF_IN_zero[OF f w])
      hence "d_IN (Sup Y) z = 0" using Y(2) by(simp add: d_IN_Sup[OF Y])
      with TER have "z \<in> SAT \<Gamma> f" using *[OF y]
        by(simp add: SAT.simps)
      with SINK[OF y] have "z \<in> TER f" by simp
      with z y show ?thesis by(auto intro: roofed_greaterI)
    qed
  qed
  then show "x \<in> RF (\<Union>f\<in>Y. TER f)" unfolding roofed_idem .
next
  fix x
  assume x: "x \<in> RF (\<Union>f\<in>Y. TER f)"
  have "x \<in> RF (RF (TER (\<Squnion>Y)))"
  proof(rule roofedI)
    fix p y
    assume p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
    from roofedD[OF x p y] obtain z f where *: "z \<in> set (x # p)"
      and **: "f \<in> Y" and TER: "z \<in> TER f" by auto
    have "z \<in> RF (TER (Sup Y))"
    proof(rule ccontr)
      assume z: "z \<notin> RF (TER (Sup Y))"
      have "wave \<Gamma> (Sup Y)" using Y(1-2) w Y(3) by(rule wave_lub)
      hence "d_OUT (Sup Y) z = 0" using z by(rule waveD_OUT)
      hence "z \<in> SINK (Sup Y)" by(simp add: SINK.simps)
      moreover have "z \<in> SAT \<Gamma> (Sup Y)" using TER SAT_Sup_upper[OF **, of \<Gamma>] by blast
      ultimately have "z \<in> TER (Sup Y)" by simp
      hence "z \<in> RF (TER (Sup Y))" by(rule roofed_greaterI)
      with z show False by contradiction
    qed
    thus "(\<exists>z\<in>set p. z \<in> RF (TER (Sup Y))) \<or> x \<in> RF (TER (Sup Y))" using * by auto
  qed
  then show "x \<in> RF (TER (\<Squnion>Y))" unfolding roofed_idem .
qed

subsection \<open>Hindered webs with reduced weights\<close>

context countable_bipartite_web begin

context
  fixes u :: "'v \<Rightarrow> ennreal"
  and \<epsilon>
  defines "\<epsilon> \<equiv> (\<integral>\<^sup>+ y. u y \<partial>count_space (B \<Gamma>))"
  assumes u_outside: "\<And>x. x \<notin> B \<Gamma> \<Longrightarrow> u x = 0"
  and finite_\<epsilon>: "\<epsilon> \<noteq> \<top>"
begin

private lemma u_A: "x \<in> A \<Gamma> \<Longrightarrow> u x = 0"
using u_outside[of x] disjoint by auto

private lemma u_finite: "u y \<noteq> \<top>"
proof(cases "y \<in> B \<Gamma>")
  case True
  have "u y \<le> \<epsilon>" unfolding \<epsilon>_def by(rule nn_integral_ge_point)(simp add: True)
  also have "\<dots> < \<top>" using finite_\<epsilon> by (simp add: less_top[symmetric])
  finally show ?thesis by simp
qed(simp add: u_outside)

lemma hindered_reduce: \<comment> \<open>Lemma 6.7\<close>
  assumes u: "u \<le> weight \<Gamma>"
  assumes hindered_by: "hindered_by (\<Gamma>\<lparr>weight := weight \<Gamma> - u\<rparr>) \<epsilon>" (is "hindered_by ?\<Gamma> _")
  shows "hindered \<Gamma>"
proof -
  note [simp] = u_finite
  let ?TER = "TER\<^bsub>?\<Gamma>\<^esub>"
  from hindered_by obtain f
    where hindrance_by: "hindrance_by ?\<Gamma> f \<epsilon>"
    and f: "current ?\<Gamma> f"
    and w: "wave ?\<Gamma> f" by cases
  from hindrance_by obtain a where a: "a \<in> A \<Gamma>" "a \<notin> \<E>\<^bsub>?\<Gamma>\<^esub> (?TER f)"
    and a_le: "d_OUT f a < weight \<Gamma> a"
    and \<epsilon>_less: "weight \<Gamma> a - d_OUT f a > \<epsilon>"
    and \<epsilon>_nonneg: "\<epsilon> \<ge> 0" by(auto simp add: u_A hindrance_by.simps)

  from f have f': "current \<Gamma> f" by(rule current_weight_mono)(auto intro: diff_le_self_ennreal)

  write Some ("\<langle>_\<rangle>")

  define edge'
    where "edge' xo yo =
      (case (xo, yo) of
        (None, Some y) \<Rightarrow> y \<in> \<^bold>V \<and> y \<notin> A \<Gamma>
      | (Some x, Some y) \<Rightarrow> edge \<Gamma> x y \<or> edge \<Gamma> y x
      | _ \<Rightarrow> False)" for xo yo
  define cap
    where "cap e =
      (case e of
        (None, Some y) \<Rightarrow> if y \<in> \<^bold>V then u y else 0
      | (Some x, Some y) \<Rightarrow> if edge \<Gamma> x y \<and> x \<noteq> a then f (x, y) else if edge \<Gamma> y x then max (weight \<Gamma> x) (weight \<Gamma> y) + 1 else 0
      | _ \<Rightarrow> 0)" for e
  define \<Psi> where "\<Psi> = \<lparr>edge = edge', capacity = cap, source = None, sink = Some a\<rparr>"

  have edge'_simps [simp]:
    "edge' None \<langle>y\<rangle> \<longleftrightarrow> y \<in> \<^bold>V \<and> y \<notin> A \<Gamma>"
    "edge' xo None \<longleftrightarrow> False"
    "edge' \<langle>x\<rangle> \<langle>y\<rangle> \<longleftrightarrow> edge \<Gamma> x y \<or> edge \<Gamma> y x"
    for xo x y by(simp_all add: edge'_def split: option.split)

  have edge_None1E [elim!]: thesis if "edge' None y" "\<And>z. \<lbrakk> y = \<langle>z\<rangle>; z \<in> \<^bold>V; z \<notin> A \<Gamma> \<rbrakk> \<Longrightarrow> thesis" for y thesis
    using that by(simp add: edge'_def split: option.split_asm sum.split_asm)
  have edge_Some1E [elim!]: thesis if "edge' \<langle>x\<rangle> y" "\<And>z. \<lbrakk> y = \<langle>z\<rangle>; edge \<Gamma> x z \<or> edge \<Gamma> z x \<rbrakk> \<Longrightarrow> thesis" for x y thesis
    using that by(simp add: edge'_def split: option.split_asm sum.split_asm)
  have edge_Some2E [elim!]: thesis if "edge' x \<langle>y\<rangle>" "\<lbrakk> x = None; y \<in> \<^bold>V; y \<notin> A \<Gamma> \<rbrakk> \<Longrightarrow> thesis" "\<And>z. \<lbrakk> x = \<langle>z\<rangle>; edge \<Gamma> z y \<or> edge \<Gamma> y z \<rbrakk> \<Longrightarrow> thesis" for x y thesis
    using that by(simp add: edge'_def split: option.split_asm sum.split_asm)

  have cap_simps [simp]:
    "cap (None, \<langle>y\<rangle>) = (if y \<in> \<^bold>V then u y else 0)"
    "cap (xo, None) = 0"
    "cap (\<langle>x\<rangle>, \<langle>y\<rangle>) =
    (if edge \<Gamma> x y \<and> x \<noteq> a then f (x, y) else if edge \<Gamma> y x then max (weight \<Gamma> x) (weight \<Gamma> y) + 1 else 0)"
    for xo x y by(simp_all add: cap_def split: option.split)

  have \<Psi>_sel [simp]:
    "edge \<Psi> = edge'"
    "capacity \<Psi> = cap"
    "source \<Psi> = None"
    "sink \<Psi> = \<langle>a\<rangle>"
    by(simp_all add: \<Psi>_def)

  have cap_outside1: "\<not> vertex \<Gamma> x \<Longrightarrow> cap (\<langle>x\<rangle>, y) = 0" for x y
    by(cases y)(auto simp add: vertex_def)
  have capacity_A_weight: "d_OUT cap \<langle>x\<rangle> \<le> weight \<Gamma> x" if "x \<in> A \<Gamma>" for x
  proof -
    have "d_OUT cap \<langle>x\<rangle> \<le> (\<Sum>\<^sup>+ y\<in>range Some. f (x, the y))"
      using that disjoint a(1) unfolding d_OUT_def
      by(auto 4 4 intro!: nn_integral_mono simp add: nn_integral_count_space_indicator notin_range_Some currentD_outside[OF f] split: split_indicator dest: edge_antiparallel bipartite_E)
    also have "\<dots> = d_OUT f x" by(simp add: d_OUT_def nn_integral_count_space_reindex)
    also have "\<dots> \<le> weight \<Gamma> x" using f' by(rule currentD_weight_OUT)
    finally show ?thesis .
  qed
  have flow_attainability: "flow_attainability \<Psi>"
  proof
    have "\<^bold>E\<^bsub>\<Psi>\<^esub> = (\<lambda>(x, y). (\<langle>x\<rangle>, \<langle>y\<rangle>)) ` \<^bold>E \<union> (\<lambda>(x, y). (\<langle>y\<rangle>, \<langle>x\<rangle>)) ` \<^bold>E \<union> (\<lambda>x. (None, \<langle>x\<rangle>)) ` (\<^bold>V \<inter> - A \<Gamma>)"
      by(auto simp add: edge'_def split: option.split_asm)
    thus "countable \<^bold>E\<^bsub>\<Psi>\<^esub>" by simp
  next
    fix v
    assume "v \<noteq> sink \<Psi>"
    consider (sink) "v = None" | (A) x where "v = \<langle>x\<rangle>" "x \<in> A \<Gamma>"
      | (B) y where "v = \<langle>y\<rangle>" "y \<notin> A \<Gamma>" "y \<in> \<^bold>V" | (outside) x where "v = \<langle>x\<rangle>" "x \<notin> \<^bold>V"
      by(cases v) auto
    then show "d_IN (capacity \<Psi>) v \<noteq> \<top> \<or> d_OUT (capacity \<Psi>) v \<noteq> \<top>"
    proof cases
      case sink thus ?thesis by(simp add: d_IN_def)
    next
      case (A x)
      thus ?thesis using capacity_A_weight[of x] by (auto simp: top_unique)
    next
      case (B y)
      have "d_IN (capacity \<Psi>) v \<le> (\<Sum>\<^sup>+ x. f (the x, y) * indicator (range Some) x + u y * indicator {None} x)"
        using B disjoint bipartite_V a(1) unfolding d_IN_def
        by(auto 4 4 intro!: nn_integral_mono simp add: nn_integral_count_space_indicator notin_range_Some currentD_outside[OF f] split: split_indicator dest: edge_antiparallel bipartite_E)
      also have "\<dots> = (\<Sum>\<^sup>+ x\<in>range Some. f (the x, y)) + u y"
        by(subst nn_integral_add)(simp_all add: nn_integral_count_space_indicator)
      also have "\<dots> = d_IN f y + u y" by(simp add: d_IN_def nn_integral_count_space_reindex)
      also have "d_IN f y \<le> weight \<Gamma> y" using f' by(rule currentD_weight_IN)
      finally show ?thesis by(auto simp add: add_right_mono top_unique split: if_split_asm)
    next
      case outside
      hence "d_OUT (capacity \<Psi>) v = 0"
        by(auto simp add: d_OUT_def nn_integral_0_iff_AE AE_count_space cap_def vertex_def split: option.split)
      thus ?thesis by simp
    qed
  next
    show "capacity \<Psi> e \<noteq> \<top>" for e using weight_finite
      by(auto simp add: cap_def max_def vertex_def currentD_finite[OF f'] split: option.split prod.split simp del: weight_finite)
    show "capacity \<Psi> e = 0" if "e \<notin> \<^bold>E\<^bsub>\<Psi>\<^esub>" for e
      using that bipartite_V disjoint
      by(auto simp add: cap_def max_def intro: u_outside split: option.split prod.split)
    show "\<not> edge \<Psi> x (source \<Psi>)" for x  by simp
    show "\<not> edge \<Psi> x x" for x by(cases x)(simp_all add: no_loop)
    show "source \<Psi> \<noteq> sink \<Psi>" by simp
  qed
  then interpret \<Psi>: flow_attainability "\<Psi>" .

  define \<alpha> where "\<alpha> = (\<Squnion>g\<in>{g. flow \<Psi> g}. value_flow \<Psi> g)"
  have \<alpha>_le: "\<alpha> \<le> \<epsilon>"
  proof -
    have "\<alpha> \<le> d_OUT cap None" unfolding \<alpha>_def by(rule SUP_least)(auto intro!: d_OUT_mono dest: flowD_capacity)
    also have "\<dots> \<le> \<integral>\<^sup>+ y. cap (None, y) \<partial>count_space (range Some)" unfolding d_OUT_def
      by(auto simp add: nn_integral_count_space_indicator notin_range_Some intro!: nn_integral_mono split: split_indicator)
    also have "\<dots> \<le> \<epsilon>" unfolding \<epsilon>_def
      by (subst (2) nn_integral_count_space_indicator, auto simp add: nn_integral_count_space_reindex u_outside intro!: nn_integral_mono split: split_indicator)
    finally show ?thesis by simp
  qed
  then have finite_flow: "\<alpha> \<noteq> \<top>" using finite_\<epsilon> by (auto simp: top_unique)

  from \<Psi>.ex_max_flow
  obtain j where j: "flow \<Psi> j"
    and value_j: "value_flow \<Psi> j = \<alpha>"
    and IN_j: "\<And>x. d_IN j x \<le> \<alpha>"
    unfolding \<alpha>_def by auto

  have j_le_f: "j (Some x, Some y) \<le> f (x, y)" if "edge \<Gamma> x y" for x y
    using that flowD_capacity[OF j, of "(Some x, Some y)"] a(1) disjoint
    by(auto split: if_split_asm dest: bipartite_E intro: order_trans)

  have IN_j_finite [simp]: "d_IN j x \<noteq> \<top>" for x using finite_flow by(rule neq_top_trans)(simp add: IN_j)

  have j_finite[simp]: "j (x, y) < \<top>" for x y
    by (rule le_less_trans[OF d_IN_ge_point]) (simp add: IN_j_finite[of y] less_top[symmetric])

  have OUT_j_finite: "d_OUT j x \<noteq> \<top>" for x
  proof(cases "x = source \<Psi> \<or> x = sink \<Psi>")
    case True thus ?thesis
    proof cases
      case left thus ?thesis using finite_flow value_j by simp
    next
      case right
      have "d_OUT (capacity \<Psi>) \<langle>a\<rangle> \<noteq> \<top>" using capacity_A_weight[of a] a(1) by(auto simp: top_unique)
      thus ?thesis unfolding right[simplified]
        by(rule neq_top_trans)(rule d_OUT_mono flowD_capacity[OF j])+
    qed
  next
    case False then show ?thesis by(simp add: flowD_KIR[OF j])
  qed

  have IN_j_le_weight: "d_IN j \<langle>x\<rangle> \<le> weight \<Gamma> x" for x
  proof(cases "x \<in> A \<Gamma>")
    case xA: True
    show ?thesis
    proof(cases "x = a")
      case True
      have "d_IN j \<langle>x\<rangle> \<le> \<alpha>" by(rule IN_j)
      also have "\<dots> \<le> \<epsilon>" by(rule \<alpha>_le)
      also have "\<epsilon> < weight \<Gamma> a" using \<epsilon>_less diff_le_self_ennreal less_le_trans by blast
      finally show ?thesis using True by(auto intro: order.strict_implies_order)
    next
      case False
      have "d_IN j \<langle>x\<rangle> = d_OUT j \<langle>x\<rangle>" using flowD_KIR[OF j, of "Some x"] False by simp
      also have "\<dots> \<le> d_OUT cap \<langle>x\<rangle>" using flowD_capacity[OF j] by(auto intro: d_OUT_mono)
      also have "\<dots> \<le> weight \<Gamma> x" using xA  by(rule capacity_A_weight)
      finally show ?thesis .
    qed
  next
    case xA: False
    show ?thesis
    proof(cases "x \<in> B \<Gamma>")
      case True
      have "d_IN j \<langle>x\<rangle> \<le> d_IN cap \<langle>x\<rangle>" using flowD_capacity[OF j] by(auto intro: d_IN_mono)
      also have "\<dots> \<le> (\<Sum>\<^sup>+ z. f (the z, x) * indicator (range Some) z) + (\<Sum>\<^sup>+ z :: 'v option. u x * indicator {None} z)"
        using True disjoint
        by(subst nn_integral_add[symmetric])(auto simp add: vertex_def currentD_outside[OF f] d_IN_def B_out intro!: nn_integral_mono split: split_indicator)
      also have "\<dots> = d_IN f x + u x"
        by(simp add: nn_integral_count_space_indicator[symmetric] nn_integral_count_space_reindex d_IN_def)
      also have "\<dots> \<le> weight \<Gamma> x" using currentD_weight_IN[OF f, of x] u_finite[of x]
        using \<epsilon>_less u by (auto simp add: ennreal_le_minus_iff le_fun_def)
      finally show ?thesis .
    next
      case False
      with xA have "x \<notin> \<^bold>V" using bipartite_V by blast
      then have "d_IN j \<langle>x\<rangle> = 0" using False
        by(auto simp add: d_IN_def nn_integral_0_iff emeasure_count_space_eq_0 vertex_def edge'_def split: option.split_asm intro!: \<Psi>.flowD_outside[OF j])
      then show ?thesis
        by simp
    qed
  qed

  let ?j = "j \<circ> map_prod Some Some \<circ> prod.swap"

  have finite_j_OUT: "(\<Sum>\<^sup>+ y\<in>\<^bold>O\<^bold>U\<^bold>T x. j (\<langle>x\<rangle>, \<langle>y\<rangle>)) \<noteq> \<top>" (is "?j_OUT \<noteq> _") if "x \<in> A \<Gamma>" for x
    using currentD_finite_OUT[OF f', of x]
    by(rule neq_top_trans)(auto intro!: nn_integral_mono j_le_f simp add: d_OUT_def nn_integral_count_space_indicator outgoing_def split: split_indicator)
  have j_OUT_eq: "?j_OUT x = d_OUT j \<langle>x\<rangle>" if "x \<in> A \<Gamma>" for x
  proof -
    have "?j_OUT x = (\<Sum>\<^sup>+ y\<in>range Some. j (Some x, y))" using that disjoint
      by(simp add: nn_integral_count_space_reindex)(auto 4 4 simp add: nn_integral_count_space_indicator outgoing_def intro!: nn_integral_cong \<Psi>.flowD_outside[OF j] dest: bipartite_E split: split_indicator)
    also have "\<dots> = d_OUT j \<langle>x\<rangle>"
      by(auto simp add: d_OUT_def nn_integral_count_space_indicator notin_range_Some intro!: nn_integral_cong \<Psi>.flowD_outside[OF j] split: split_indicator)
    finally show ?thesis .
  qed

  define g where "g = f \<oplus> ?j"
  have g_simps: "g (x, y) = (f \<oplus> ?j) (x, y)" for x y by(simp add: g_def)

  have OUT_g_A: "d_OUT g x = d_OUT f x + d_IN j \<langle>x\<rangle> - d_OUT j \<langle>x\<rangle>" if "x \<in> A \<Gamma>" for x
  proof -
    have "d_OUT g x = (\<Sum>\<^sup>+ y\<in>\<^bold>O\<^bold>U\<^bold>T x. f (x, y) + j (\<langle>y\<rangle>, \<langle>x\<rangle>) - j (\<langle>x\<rangle>, \<langle>y\<rangle>))"
      by(auto simp add: d_OUT_def g_simps currentD_outside[OF f'] outgoing_def nn_integral_count_space_indicator intro!: nn_integral_cong)
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>\<^bold>O\<^bold>U\<^bold>T x. f (x, y) + j (\<langle>y\<rangle>, \<langle>x\<rangle>)) - (\<Sum>\<^sup>+ y\<in>\<^bold>O\<^bold>U\<^bold>T x. j (\<langle>x\<rangle>, \<langle>y\<rangle>))"
      (is "_ = _ - ?j_OUT") using finite_j_OUT[OF that]
      by(subst nn_integral_diff)(auto simp add: AE_count_space outgoing_def intro!: order_trans[OF j_le_f])
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>\<^bold>O\<^bold>U\<^bold>T x. f (x, y)) + (\<Sum>\<^sup>+ y\<in>\<^bold>O\<^bold>U\<^bold>T x. j (Some y, Some x)) - ?j_OUT"
      (is "_ = ?f + ?j_IN - _") by(subst nn_integral_add) simp_all
    also have "?f = d_OUT f x" by(subst d_OUT_alt_def[where G=\<Gamma>])(simp_all add: currentD_outside[OF f])
    also have "?j_OUT = d_OUT j \<langle>x\<rangle>" using that by(rule j_OUT_eq)
    also have "?j_IN = (\<Sum>\<^sup>+ y\<in>range Some. j (y, \<langle>x\<rangle>))" using that disjoint
      by(simp add: nn_integral_count_space_reindex)(auto 4 4 simp add: nn_integral_count_space_indicator outgoing_def intro!: nn_integral_cong \<Psi>.flowD_outside[OF j] split: split_indicator dest: bipartite_E)
    also have "\<dots> = d_IN j (Some x)" using that disjoint
      by(auto 4 3 simp add: d_IN_def nn_integral_count_space_indicator notin_range_Some intro!: nn_integral_cong \<Psi>.flowD_outside[OF j] split: split_indicator)
    finally show ?thesis by simp
  qed

  have OUT_g_B: "d_OUT g x = 0" if "x \<notin> A \<Gamma>" for x
    using disjoint that
    by(auto simp add: d_OUT_def nn_integral_0_iff_AE AE_count_space g_simps dest: bipartite_E)

  have OUT_g_a: "d_OUT g a < weight \<Gamma> a" using a(1)
  proof -
    have "d_OUT g a = d_OUT f a + d_IN j \<langle>a\<rangle> - d_OUT j \<langle>a\<rangle>" using a(1) by(rule OUT_g_A)
    also have "\<dots> \<le> d_OUT f a + d_IN j \<langle>a\<rangle>"
      by(rule diff_le_self_ennreal)
    also have "\<dots> < weight \<Gamma> a + d_IN j \<langle>a\<rangle> - \<epsilon>"
      using finite_\<epsilon> \<epsilon>_less currentD_finite_OUT[OF f']
      by (simp add: less_diff_eq_ennreal less_top ac_simps)
    also have "\<dots> \<le> weight \<Gamma> a"
      using IN_j[THEN order_trans, OF \<alpha>_le] by (simp add: ennreal_minus_le_iff)
    finally show ?thesis .
  qed

  have OUT_jj: "d_OUT ?j x = d_IN j \<langle>x\<rangle> - j (None, \<langle>x\<rangle>)" for x
  proof -
    have "d_OUT ?j x = (\<Sum>\<^sup>+ y\<in>range Some. j (y, \<langle>x\<rangle>))" by(simp add: d_OUT_def nn_integral_count_space_reindex)
    also have "\<dots> = d_IN j \<langle>x\<rangle> - (\<Sum>\<^sup>+ y. j (y, \<langle>x\<rangle>) * indicator {None} y)" unfolding d_IN_def
      by(subst nn_integral_diff[symmetric])(auto simp add: max_def \<Psi>.flowD_finite[OF j] AE_count_space nn_integral_count_space_indicator split: split_indicator intro!: nn_integral_cong)
    also have "\<dots> = d_IN j \<langle>x\<rangle> - j (None, \<langle>x\<rangle>)" by(simp add: max_def)
    finally show ?thesis .
  qed

  have OUT_jj_finite [simp]: "d_OUT ?j x \<noteq> \<top>" for x
    by(simp add: OUT_jj)

  have IN_g: "d_IN g x = d_IN f x + j (None, \<langle>x\<rangle>)" for x
  proof(cases "x \<in> B \<Gamma>")
    case True
    have finite: "(\<Sum>\<^sup>+ y\<in>\<^bold>I\<^bold>N x. j (Some y, Some x)) \<noteq> \<top>" using currentD_finite_IN[OF f', of x]
      by(rule neq_top_trans)(auto intro!: nn_integral_mono j_le_f simp add: d_IN_def nn_integral_count_space_indicator incoming_def split: split_indicator)

    have "d_IN g x = d_IN (f \<oplus> ?j) x" by(simp add: g_def)
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>\<^bold>I\<^bold>N x. f (y, x) + j (Some x, Some y) - j (Some y, Some x))"
      by(auto simp add: d_IN_def currentD_outside[OF f'] incoming_def nn_integral_count_space_indicator intro!: nn_integral_cong)
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>\<^bold>I\<^bold>N x. f (y, x) + j (Some x, Some y)) - (\<Sum>\<^sup>+ y\<in>\<^bold>I\<^bold>N x. j (Some y, Some x))"
      (is "_ = _ - ?j_IN") using finite
      by(subst nn_integral_diff)(auto simp add: AE_count_space incoming_def intro!: order_trans[OF j_le_f])
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>\<^bold>I\<^bold>N x. f (y, x)) + (\<Sum>\<^sup>+ y\<in>\<^bold>I\<^bold>N x. j (Some x, Some y)) - ?j_IN"
      (is "_ = ?f + ?j_OUT - _") by(subst nn_integral_add) simp_all
    also have "?f = d_IN f x" by(subst d_IN_alt_def[where G=\<Gamma>])(simp_all add: currentD_outside[OF f])
    also have "?j_OUT = (\<Sum>\<^sup>+ y\<in>range Some. j (Some x, y))" using True disjoint
      by(simp add: nn_integral_count_space_reindex)(auto 4 4 simp add: nn_integral_count_space_indicator incoming_def intro!: nn_integral_cong \<Psi>.flowD_outside[OF j] split: split_indicator dest: bipartite_E)
    also have "\<dots> = d_OUT j (Some x)" using disjoint
      by(auto 4 3 simp add: d_OUT_def nn_integral_count_space_indicator notin_range_Some intro!: nn_integral_cong \<Psi>.flowD_outside[OF j] split: split_indicator)
    also have "\<dots> = d_IN j (Some x)" using flowD_KIR[OF j, of "Some x"] True a disjoint by auto
    also have "?j_IN = (\<Sum>\<^sup>+ y\<in>range Some. j (y, Some x))" using True disjoint
      by(simp add: nn_integral_count_space_reindex)(auto 4 4 simp add: nn_integral_count_space_indicator incoming_def intro!: nn_integral_cong \<Psi>.flowD_outside[OF j] dest: bipartite_E split: split_indicator)
    also have "\<dots> = d_IN j (Some x) - (\<Sum>\<^sup>+ y :: 'v option. j (None, Some x) * indicator {None} y)"
      unfolding d_IN_def using flowD_capacity[OF j, of "(None, Some x)"]
      by(subst nn_integral_diff[symmetric])
        (auto simp add: nn_integral_count_space_indicator AE_count_space top_unique image_iff
              intro!: nn_integral_cong ennreal_diff_self split: split_indicator if_split_asm)
    also have "d_IN f x + d_IN j (Some x) - \<dots> = d_IN f x + j (None, Some x)"
      using ennreal_add_diff_cancel_right[OF IN_j_finite[of "Some x"], of "d_IN f x + j (None, Some x)"]
      apply(subst diff_diff_ennreal')
      apply(auto simp add: d_IN_def intro!: nn_integral_ge_point ennreal_diff_le_mono_left)
      apply(simp add: ac_simps)
      done
    finally show ?thesis .
  next
    case False
    hence "d_IN g x = 0" "d_IN f x = 0" "j (None, \<langle>x\<rangle>) = 0"
      using disjoint currentD_IN[OF f', of x] bipartite_V currentD_outside_IN[OF f'] u_outside[OF False] flowD_capacity[OF j, of "(None, \<langle>x\<rangle>)"]
      by(cases "vertex \<Gamma> x"; auto simp add: d_IN_def nn_integral_0_iff_AE AE_count_space g_simps dest: bipartite_E split: if_split_asm)+
    thus ?thesis by simp
  qed

  have g: "current \<Gamma> g"
  proof
    show "d_OUT g x \<le> weight \<Gamma> x" for x
    proof(cases "x \<in> A \<Gamma>")
      case False
      thus ?thesis by(simp add: OUT_g_B)
    next
      case True
      with OUT_g_a show ?thesis
        by(cases "x = a")(simp_all add: OUT_g_A flowD_KIR[OF j] currentD_weight_OUT[OF f'])
    qed

    show "d_IN g x \<le> weight \<Gamma> x" for x
    proof(cases "x \<in> B \<Gamma>")
      case False
      hence "d_IN g x = 0" using disjoint
        by(auto simp add: d_IN_def nn_integral_0_iff_AE AE_count_space g_simps dest: bipartite_E)
      thus ?thesis by simp
    next
      case True
      have "d_IN g x \<le> (weight \<Gamma> x - u x) + u x" unfolding IN_g
        using currentD_weight_IN[OF f, of x] flowD_capacity[OF j, of "(None, Some x)"] True bipartite_V
        by(intro add_mono)(simp_all split: if_split_asm)
      also have "\<dots> = weight \<Gamma> x"
        using u by (intro diff_add_cancel_ennreal) (simp add: le_fun_def)
      finally show ?thesis .
    qed
    show "g e = 0" if "e \<notin> \<^bold>E" for e using that
      by(cases e)(auto simp add: g_simps)
  qed

  define cap' where "cap' = (\<lambda>(x, y). if edge \<Gamma> x y then g (x, y) else if edge \<Gamma> y x then 1 else 0)"

  have cap'_simps [simp]: "cap' (x, y) = (if edge \<Gamma> x y then g (x, y) else if edge \<Gamma> y x then 1 else 0)"
    for x y by(simp add: cap'_def)

  define G where "G = \<lparr>edge = \<lambda>x y. cap' (x, y) > 0\<rparr>"
  have G_sel [simp]: "edge G x y \<longleftrightarrow> cap' (x, y) > 0" for x y by(simp add: G_def)
  define reachable where "reachable x = (edge G)\<^sup>*\<^sup>* x a" for x
  have reachable_alt_def: "reachable \<equiv> \<lambda>x. \<exists>p. path G x p a"
    by(simp add: reachable_def [abs_def] rtranclp_eq_rtrancl_path)

  have [simp]: "reachable a" by(auto simp add: reachable_def)

  have AB_edge: "edge G x y" if "edge \<Gamma> y x" for x y
    using that
    by(auto dest: edge_antiparallel simp add: min_def le_neq_trans add_eq_0_iff_both_eq_0)
  have reachable_AB: "reachable y" if "reachable x" "(x, y) \<in> \<^bold>E" for x y
    using that by(auto simp add: reachable_def simp del: G_sel dest!: AB_edge intro: rtrancl_path.step)
  have reachable_BA: "g (x, y) = 0" if "reachable y" "(x, y) \<in> \<^bold>E" "\<not> reachable x" for x y
  proof(rule ccontr)
    assume "g (x, y) \<noteq> 0"
    then have "g (x, y) > 0" by (simp add: zero_less_iff_neq_zero)
    hence "edge G x y" using that by simp
    then have "reachable x" using \<open>reachable y\<close>
      unfolding reachable_def by(rule converse_rtranclp_into_rtranclp)
    with \<open>\<not> reachable x\<close> show False by contradiction
  qed
  have reachable_V: "vertex \<Gamma> x" if "reachable x" for x
  proof -
    from that obtain p where p: "path G x p a" unfolding reachable_alt_def ..
    then show ?thesis using rtrancl_path_nth[OF p, of 0] a(1) A_vertex
      by(cases "p = []")(auto 4 3 simp add: vertex_def elim: rtrancl_path.cases split: if_split_asm)
  qed

  have finite_j_IN: "(\<integral>\<^sup>+ y. j (Some y, Some x) \<partial>count_space (\<^bold>I\<^bold>N x)) \<noteq> \<top>" for x
  proof -
    have "(\<integral>\<^sup>+ y. j (Some y, Some x) \<partial>count_space (\<^bold>I\<^bold>N x)) \<le> d_IN f x"
      by(auto intro!: nn_integral_mono j_le_f simp add: d_IN_def nn_integral_count_space_indicator incoming_def split: split_indicator)
    thus ?thesis using currentD_finite_IN[OF f', of x] by (auto simp: top_unique)
  qed
  have j_outside: "j (x, y) = 0" if "\<not> edge \<Psi> x y" for x y
    using that flowD_capacity[OF j, of "(x, y)"] \<Psi>.capacity_outside[of "(x, y)"]
    by(auto)

  define h where "h = (\<lambda>(x, y). if reachable x \<and> reachable y then g (x, y) else 0)"
  have h_simps [simp]: "h (x, y) = (if reachable x \<and> reachable y then g (x, y) else 0)" for x y
    by(simp add: h_def)
  have h_le_g: "h e \<le> g e" for e by(cases e) simp

  have OUT_h: "d_OUT h x = (if reachable x then d_OUT g x else 0)" for x
  proof -
    have "d_OUT h x = (\<Sum>\<^sup>+ y\<in>\<^bold>O\<^bold>U\<^bold>T x. h (x, y))" using h_le_g currentD_outside[OF g]
      by(intro d_OUT_alt_def) auto
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>\<^bold>O\<^bold>U\<^bold>T x. if reachable x then g (x, y) else 0)"
      by(auto intro!: nn_integral_cong simp add: outgoing_def dest: reachable_AB)
    also have "\<dots> = (if reachable x then d_OUT g x else 0)"
      by(auto intro!: d_OUT_alt_def[symmetric] currentD_outside[OF g])
    finally show ?thesis .
  qed
  have IN_h: "d_IN h x = (if reachable x then d_IN g x else 0)" for x
  proof -
    have "d_IN h x = (\<Sum>\<^sup>+ y\<in>\<^bold>I\<^bold>N x. h (y, x))"
      using h_le_g currentD_outside[OF g] by(intro d_IN_alt_def) auto
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>\<^bold>I\<^bold>N x. if reachable x then g (y, x) else 0)"
      by(auto intro!: nn_integral_cong simp add: incoming_def dest: reachable_BA)
    also have "\<dots> = (if reachable x then d_IN g x else 0)"
      by(auto intro!: d_IN_alt_def[symmetric] currentD_outside[OF g])
    finally show ?thesis .
  qed

  have h: "current \<Gamma> h" using g h_le_g
  proof(rule current_leI)
    show "d_OUT h x \<le> d_IN h x" if "x \<notin> A \<Gamma>" for x
      by(simp add: OUT_h IN_h currentD_OUT_IN[OF g that])
  qed

  have reachable_full: "j (None, \<langle>y\<rangle>) = u y" if reach: "reachable y" for y
  proof(rule ccontr)
    assume "j (None, \<langle>y\<rangle>) \<noteq> u y"
    with flowD_capacity[OF j, of "(None, \<langle>y\<rangle>)"]
    have le: "j (None, \<langle>y\<rangle>) < u y" by(auto split: if_split_asm simp add: u_outside \<Psi>.flowD_outside[OF j] zero_less_iff_neq_zero)
    then obtain y: "y \<in> B \<Gamma>" and uy: "u y > 0" using u_outside[of y]
      by(cases "y \<in> B \<Gamma>"; cases "u y = 0") (auto simp add: zero_less_iff_neq_zero)

    from reach obtain q where q: "path G y q a" and distinct: "distinct (y # q)"
      unfolding reachable_alt_def by(auto elim: rtrancl_path_distinct)
    have q_Nil: "q \<noteq> []" using q a(1) disjoint y by(auto elim!: rtrancl_path.cases)

    let ?E = "zip (y # q) q"
    define E where "E = (None, Some y) # map (map_prod Some Some) ?E"
    define \<zeta> where "\<zeta> = Min (insert (u y - j (None, Some y)) (cap' ` set ?E))"
    let ?j' = "\<lambda>e. (if e \<in> set E then \<zeta> else 0) + j e"
    define j' where "j' = cleanup ?j'"

    have j_free: "0 < cap' e" if "e \<in> set ?E" for e using that unfolding E_def list.sel
    proof -
      from that obtain i where e: "e = ((y # q) ! i, q ! i)"
        and i: "i < length q" by(auto simp add: set_zip)
      have e': "edge G ((y # q) ! i) (q ! i)" using q i by(rule rtrancl_path_nth)
      thus ?thesis using e by(simp)
    qed
    have \<zeta>_pos: "0 < \<zeta>" unfolding \<zeta>_def using le
      by(auto intro: j_free diff_gr0_ennreal)
    have \<zeta>_le: "\<zeta> \<le> cap' e" if "e \<in> set ?E" for e using that unfolding \<zeta>_def by auto
    have finite_\<zeta> [simplified]: "\<zeta> < \<top>" unfolding \<zeta>_def
      by(intro Min_less_iff[THEN iffD2])(auto simp add: less_top[symmetric])

    have E_antiparallel: "(x', y') \<in> set ?E \<Longrightarrow> (y', x') \<notin> set ?E" for x' y'
      using distinct
      apply(auto simp add: in_set_zip nth_Cons in_set_conv_nth)
      apply(auto simp add: distinct_conv_nth split: nat.split_asm)
      by (metis Suc_lessD less_Suc_eq less_irrefl_nat)

    have OUT_j': "d_OUT ?j' x' = \<zeta> * card (set [(x'', y) \<leftarrow> E. x'' = x']) + d_OUT j x'" for x'
    proof -
      have "d_OUT ?j' x' = d_OUT (\<lambda>e. if e \<in> set E then \<zeta> else 0) x' + d_OUT j x'"
        using \<zeta>_pos by(intro d_OUT_add)
      also have "d_OUT (\<lambda>e. if e \<in> set E then \<zeta> else 0) x' = \<integral>\<^sup>+ y. \<zeta> * indicator (set E) (x', y) \<partial>count_space UNIV"
        unfolding d_OUT_def by(rule nn_integral_cong)(simp)
      also have "\<dots> = (\<integral>\<^sup>+ e. \<zeta> * indicator (set E) e \<partial>embed_measure (count_space UNIV) (Pair x'))"
        by(simp add: measurable_embed_measure1 nn_integral_embed_measure)
      also have "\<dots> = (\<integral>\<^sup>+ e. \<zeta> * indicator (set [(x'', y) \<leftarrow> E. x'' = x']) e \<partial>count_space UNIV)"
        by(auto simp add: embed_measure_count_space' nn_integral_count_space_indicator intro!: nn_integral_cong split: split_indicator)
      also have "\<dots> = \<zeta> * card (set [(x'', y) \<leftarrow> E. x'' = x'])" using \<zeta>_pos by(simp add: nn_integral_cmult)
      finally show ?thesis .
    qed
    have IN_j': "d_IN ?j' x' = \<zeta> * card (set [(y, x'') \<leftarrow> E. x'' = x']) + d_IN j x'" for x'
    proof -
      have "d_IN ?j' x' = d_IN (\<lambda>e. if e \<in> set E then \<zeta> else 0) x' + d_IN j x'"
        using \<zeta>_pos by(intro d_IN_add)
      also have "d_IN (\<lambda>e. if e \<in> set E then \<zeta> else 0) x' = \<integral>\<^sup>+ y. \<zeta> * indicator (set E) (y, x') \<partial>count_space UNIV"
        unfolding d_IN_def by(rule nn_integral_cong)(simp)
      also have "\<dots> = (\<integral>\<^sup>+ e. \<zeta> * indicator (set E) e \<partial>embed_measure (count_space UNIV) (\<lambda>y. (y, x')))"
        by(simp add: measurable_embed_measure1 nn_integral_embed_measure)
      also have "\<dots> = (\<integral>\<^sup>+ e. \<zeta> * indicator (set [(y, x'') \<leftarrow> E. x'' = x']) e \<partial>count_space UNIV)"
        by(auto simp add: embed_measure_count_space' nn_integral_count_space_indicator intro!: nn_integral_cong split: split_indicator)
      also have "\<dots> = \<zeta> * card (set [(y, x'') \<leftarrow> E. x'' = x'])"
        using \<zeta>_pos by(auto simp add: nn_integral_cmult)
      finally show ?thesis .
    qed

    have j': "flow \<Psi> j'"
    proof
      fix e :: "'v option edge"
      consider (None) "e = (None, Some y)"
        | (Some) x y where "e = (Some x, Some y)" "(x, y) \<in> set ?E"
        | (old) x y where "e = (Some x, Some y)" "(x, y) \<notin> set ?E"
        | y' where "e = (None, Some y')" "y \<noteq> y'"
        | "e = (None, None)" | x where "e = (Some x, None)"
        by(cases e; case_tac a; case_tac b)(auto)
      then show "j' e \<le> capacity \<Psi> e" using uy \<zeta>_pos flowD_capacity[OF j, of e]
      proof(cases)
        case None
        have "\<zeta> \<le> u y - j (None, Some y)" by(simp add: \<zeta>_def)
        then have "\<zeta> + j (None, Some y) \<le> u y"
          using \<zeta>_pos by (auto simp add: ennreal_le_minus_iff)
        thus ?thesis using reachable_V[OF reach] None \<Psi>.flowD_outside[OF j, of "(Some y, None)"] uy
          by(auto simp add: j'_def E_def)
      next
        case (Some x' y')
        have e: "\<zeta> \<le> cap' (x', y')" using Some(2) by(rule \<zeta>_le)
        then consider (backward) "edge \<Gamma> x' y'" "x' \<noteq> a" | (forward) "edge \<Gamma> y' x'" "\<not> edge \<Gamma> x' y'"
          | (a') "edge \<Gamma> x' y'" "x' = a"
          using Some \<zeta>_pos by(auto split: if_split_asm)
        then show ?thesis
        proof cases
          case backward
          have "\<zeta> \<le> f (x', y') + j (Some y', Some x') - j (Some x', Some y')"
            using e backward Some(1) by(simp add: g_simps)
          hence "\<zeta> + j (Some x', Some y') - j (Some y', Some x') \<le> (f (x', y') + j (Some y', Some x') - j (Some x', Some y')) + j (Some x', Some y') - j (Some y', Some x')"
            by(intro ennreal_minus_mono add_right_mono) simp_all
          also have "\<dots> = f (x', y')"
            using j_le_f[OF \<open>edge \<Gamma> x' y'\<close>]
            by(simp_all add: add_increasing2 less_top diff_add_assoc2_ennreal)
          finally show ?thesis using Some backward
            by(auto simp add: j'_def E_def dest: in_set_tlD E_antiparallel)
        next
          case forward
          have "\<zeta> + j (Some x', Some y') - j (Some y', Some x') \<le> \<zeta> + j (Some x', Some y')"
            by(rule diff_le_self_ennreal)
          also have "j (Some x', Some y') \<le> d_IN j (Some y')"
            by(rule d_IN_ge_point)
          also have "\<dots> \<le> weight \<Gamma> y'" by(rule IN_j_le_weight)
          also have "\<zeta> \<le> 1" using e forward by simp
          finally have "\<zeta> + j (Some x', Some y') - j (Some y', Some x') \<le> max (weight \<Gamma> x') (weight \<Gamma> y') + 1"
            by(simp add: add_left_mono add_right_mono max_def)(metis (no_types, lifting) add.commute add_right_mono less_imp_le less_le_trans not_le)
          then show ?thesis using Some forward e
            by(auto simp add: j'_def E_def max_def dest: in_set_tlD E_antiparallel)
        next
          case a'
          with Some have "a \<in> set (map fst (zip (y # q) q))" by(auto intro: rev_image_eqI)
          also have "map fst (zip (y # q) q) = butlast (y # q)" by(induction q arbitrary: y) auto
          finally have False using rtrancl_path_last[OF q q_Nil] distinct q_Nil
            by(cases q rule: rev_cases) auto
          then show ?thesis ..
        qed
      next
        case (old x' y')
        hence "j' e \<le> j e" using \<zeta>_pos
          by(auto simp add: j'_def E_def intro!: diff_le_self_ennreal)
        also have "j e \<le> capacity \<Psi> e" using j by(rule flowD_capacity)
        finally show ?thesis .
      qed(auto simp add: j'_def E_def \<Psi>.flowD_outside[OF j] uy)
    next
      fix x'
      assume x': "x' \<noteq> source \<Psi>" "x' \<noteq> sink \<Psi>"
      then obtain x'' where x'': "x' = Some x''" by auto
      have "d_OUT ?j' x' = \<zeta> * card (set [(x'', y) \<leftarrow> E. x'' = x']) + d_OUT j x'" by(rule OUT_j')
      also have "card (set [(x'', y) \<leftarrow> E. x'' = x']) = card (set [(y, x'') \<leftarrow> E. x'' = x'])" (is "?lhs = ?rhs")
      proof -
        have "?lhs = length [(x'', y) \<leftarrow> E. x'' = x']" using distinct
          by(subst distinct_card)(auto simp add: E_def filter_map distinct_map inj_map_prod' distinct_zipI1)
        also have "\<dots> = length [x''' \<leftarrow> map fst ?E. x''' = x'']"
          by(simp add: E_def x'' split_beta cong: filter_cong)
        also have "map fst ?E = butlast (y # q)" by(induction q arbitrary: y) simp_all
        also have "[x''' \<leftarrow> butlast (y # q). x''' = x''] = [x''' \<leftarrow> y # q. x''' = x'']"
          using q_Nil rtrancl_path_last[OF q q_Nil] x' x''
          by(cases q rule: rev_cases) simp_all
        also have "q = map snd ?E" by(induction q arbitrary: y) auto
        also have "length [x''' \<leftarrow> y # \<dots>. x''' = x''] = length [x'' \<leftarrow> map snd E. x'' = x']" using x''
          by(simp add: E_def cong: filter_cong)
        also have "\<dots> = length [(y, x'') \<leftarrow> E. x'' = x']" by(simp cong: filter_cong add: split_beta)
        also have "\<dots> = ?rhs" using distinct
          by(subst distinct_card)(auto simp add: E_def filter_map distinct_map inj_map_prod' distinct_zipI1)
        finally show ?thesis .
      qed
      also have "\<zeta> * \<dots> + d_OUT j x' =  d_IN ?j' x'"
        unfolding flowD_KIR[OF j x'] by(rule IN_j'[symmetric])
      also have "d_IN ?j' x' \<noteq> \<top>"
        using \<Psi>.flowD_finite_IN[OF j x'(2)] finite_\<zeta> IN_j'[of x'] by (auto simp: top_add ennreal_mult_eq_top_iff)
      ultimately show "KIR j' x'" unfolding j'_def by(rule KIR_cleanup)
    qed
    hence "value_flow \<Psi> j' \<le> \<alpha>" unfolding \<alpha>_def by(auto intro: SUP_upper)
    moreover have "value_flow \<Psi> j' > value_flow \<Psi> j"
    proof -
      have "value_flow \<Psi> j + 0 < value_flow \<Psi> j + \<zeta> * 1"
        using \<zeta>_pos value_j finite_flow by simp
      also have "[(x', y') \<leftarrow> E. x' = None] = [(None, Some y)]"
        using q_Nil by(cases q)(auto simp add: E_def filter_map cong: filter_cong split_beta)
      hence "\<zeta> * 1 \<le> \<zeta> * card (set [(x', y') \<leftarrow> E. x' = None])" using \<zeta>_pos
        by(intro mult_left_mono)(auto simp add: E_def real_of_nat_ge_one_iff neq_Nil_conv card.insert_remove)
      also have "value_flow \<Psi> j + \<dots> = value_flow \<Psi> ?j'"
        using OUT_j' by(simp add: add.commute)
      also have "\<dots> = value_flow \<Psi> j'" unfolding j'_def
        by(subst value_flow_cleanup)(auto simp add: E_def \<Psi>.flowD_outside[OF j])
      finally show ?thesis by(simp add: add_left_mono)
    qed
    ultimately show False using finite_flow \<zeta>_pos value_j
      by(cases "value_flow \<Psi> j" \<zeta> rule: ennreal2_cases) simp_all
  qed

  have sep_h: "y \<in> TER h" if reach: "reachable y" and y: "y \<in> B \<Gamma>" and TER: "y \<in> ?TER f" for y
  proof(rule ccontr)
    assume y': "y \<notin> TER h"
    from y a(1) disjoint have yna: "y \<noteq> a" by auto

    from reach obtain p' where "path G y p' a" unfolding reachable_alt_def ..
    then obtain p' where p': "path G y p' a" and distinct: "distinct (y # p')" by(rule rtrancl_path_distinct)

    have SINK: "y \<in> SINK h" using y disjoint
      by(auto simp add: SINK.simps d_OUT_def nn_integral_0_iff emeasure_count_space_eq_0 intro: currentD_outside[OF g] dest: bipartite_E)
    have hg: "d_IN h y = d_IN g y" using reach by(simp add: IN_h)
    also have "\<dots> = d_IN f y + j (None, Some y)" by(simp add: IN_g)
    also have "d_IN f y = weight \<Gamma> y - u y" using currentD_weight_IN[OF f, of y] y disjoint TER
      by(auto elim!: SAT.cases)
    also have "d_IN h y < weight \<Gamma> y" using y' currentD_weight_IN[OF g, of y] y disjoint SINK
      by(auto intro: SAT.intros)
    ultimately have le: "j (None, Some y) < u y"
      by(cases "weight \<Gamma> y" "u y" "j (None, Some y)" rule: ennreal3_cases; cases "u y \<le> weight \<Gamma> y")
        (auto simp: ennreal_minus ennreal_plus[symmetric] add_top ennreal_less_iff ennreal_neg simp del: ennreal_plus)
    moreover from reach have "j (None, \<langle>y\<rangle>) = u y" by(rule reachable_full)
    ultimately show False by simp
  qed

  have w': "wave \<Gamma> h"
  proof
    show sep: "separating \<Gamma> (TER h)"
    proof(rule ccontr)
      assume "\<not> ?thesis"
      then obtain x p y where x: "x \<in> A \<Gamma>" and y: "y \<in> B \<Gamma>" and p: "path \<Gamma> x p y"
        and x': "x \<notin> TER h" and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> TER h"
        by(auto simp add: separating_gen.simps)
      from p disjoint x y have p_eq: "p = [y]" and edge: "(x, y) \<in> \<^bold>E"
        by -(erule rtrancl_path.cases, auto dest: bipartite_E)+
      from p_eq bypass have y': "y \<notin> TER h" by simp
      have "reachable x" using x' by(rule contrapos_np)(simp add: SINK.simps d_OUT_def SAT.A x)
      hence reach: "reachable y" using edge by(rule reachable_AB)

      have *: "x \<notin> \<E>\<^bsub>?\<Gamma>\<^esub> (?TER f)" using x'
      proof(rule contrapos_nn)
        assume *: "x \<in> \<E>\<^bsub>?\<Gamma>\<^esub> (?TER f)"
        have "d_OUT h x \<le> d_OUT g x" using h_le_g by(rule d_OUT_mono)
        also from * have "x \<noteq> a" using a by auto
        then have "d_OUT j (Some x) = d_IN j (Some x)" by(auto intro: flowD_KIR[OF j])
        hence "d_OUT g x \<le> d_OUT f x" using OUT_g_A[OF x] IN_j[of "Some x"] finite_flow
          by(auto split: if_split_asm)
        also have "\<dots> = 0" using * by(auto elim: SINK.cases)
        finally have "x \<in> SINK h" by(simp add: SINK.simps)
        with x show "x \<in> TER h" by(simp add: SAT.A)
      qed
      from p p_eq x y have "path ?\<Gamma> x [y] y" "x \<in> A ?\<Gamma>" "y \<in> B ?\<Gamma>" by simp_all
      from * separatingD[OF separating_essential, OF waveD_separating, OF w this]
      have "y \<in> ?TER f" by auto
      with reach y have "y \<in> TER h" by(rule sep_h)
      with y' show False by contradiction
    qed
  qed(rule h)

  have OUT_g_a: "d_OUT g a = d_OUT h a" by(simp add: OUT_h)
  have "a \<notin> \<E> (TER h)"
  proof
    assume *: "a \<in> \<E> (TER h)"

    have "j (Some a, Some y) = 0" for y
      using flowD_capacity[OF j, of "(Some a, Some y)"] a(1) disjoint
      by(auto split: if_split_asm dest: bipartite_E)
    then have "d_OUT f a \<le> d_OUT g a" unfolding d_OUT_def
      \<comment> \<open>This step requires that @{term j} does not decrease the outflow of @{term a}. That's
          why we set the capacity of the outgoing edges from @{term "Some a"} in @{term \<Psi>} to @{term "0 :: ennreal"}\<close>
      by(intro nn_integral_mono)(auto simp add: g_simps currentD_outside[OF f] intro: )
    then have "a \<in> SINK f" using OUT_g_a * by(simp add: SINK.simps)
    with a(1) have "a \<in> ?TER f" by(auto intro: SAT.A)
    with a(2) have a': "\<not> essential \<Gamma> (B \<Gamma>) (?TER f) a" by simp

    from * obtain y where ay: "edge \<Gamma> a y" and y: "y \<in> B \<Gamma>" and y': "y \<notin> TER h" using disjoint a(1)
      by(auto 4 4 simp add: essential_def elim: rtrancl_path.cases dest: bipartite_E)
    from not_essentialD[OF a' rtrancl_path.step, OF ay rtrancl_path.base y]
    have TER: "y \<in> ?TER f" by simp

    have "reachable y" using \<open>reachable a\<close> by(rule reachable_AB)(simp add: ay)
    hence "y \<in> TER h" using y TER by(rule sep_h)
    with y' show False by contradiction
  qed
  with \<open>a \<in> A \<Gamma>\<close> have "hindrance \<Gamma> h"
  proof
    have "d_OUT h a = d_OUT g a" by(simp add: OUT_g_a)
    also have "\<dots> \<le> d_OUT f a + \<integral>\<^sup>+ y. j (Some y, Some a) \<partial>count_space UNIV"
      unfolding d_OUT_def d_IN_def
      by(subst nn_integral_add[symmetric])(auto simp add: g_simps intro!: nn_integral_mono diff_le_self_ennreal)
    also have "(\<integral>\<^sup>+ y. j (Some y, Some a) \<partial>count_space UNIV) = (\<integral>\<^sup>+ y. j (y, Some a) \<partial>embed_measure (count_space UNIV) Some)"
      by(simp add: nn_integral_embed_measure measurable_embed_measure1)
    also have "\<dots> \<le> d_IN j (Some a)" unfolding d_IN_def
      by(auto simp add: embed_measure_count_space nn_integral_count_space_indicator intro!: nn_integral_mono split: split_indicator)
    also have "\<dots> \<le> \<alpha>" by(rule IN_j)
    also have "\<dots> \<le> \<epsilon>" by(rule \<alpha>_le)
    also have "d_OUT f a + \<dots> < d_OUT f a + (weight \<Gamma> a - d_OUT f a)" using \<epsilon>_less
      using currentD_finite_OUT[OF f'] by (simp add: ennreal_add_left_cancel_less)
    also have "\<dots> = weight \<Gamma> a"
      using a_le by simp
    finally show "d_OUT h a < weight \<Gamma> a" by(simp add: add_left_mono)
  qed
  then show ?thesis using h w' by(blast intro: hindered.intros)
qed

end

corollary hindered_reduce_current: \<comment> \<open>Corollary 6.8\<close>
  fixes \<epsilon> g
  defines "\<epsilon> \<equiv> \<Sum>\<^sup>+ x\<in>B \<Gamma>. d_IN g x - d_OUT g x"
  assumes g: "current \<Gamma> g"
  and \<epsilon>_finite: "\<epsilon> \<noteq> \<top>"
  and hindered: "hindered_by (\<Gamma> \<ominus> g) \<epsilon>"
  shows "hindered \<Gamma>"
proof -
  define \<Gamma>' where "\<Gamma>' = \<Gamma>\<lparr>weight := \<lambda>x. if x \<in> A \<Gamma> then weight \<Gamma> x - d_OUT g x else weight \<Gamma> x\<rparr>"
  have \<Gamma>'_sel [simp]:
    "edge \<Gamma>' = edge \<Gamma>"
    "A \<Gamma>' = A \<Gamma>"
    "B \<Gamma>' = B \<Gamma>"
    "weight \<Gamma>' x = (if x \<in> A \<Gamma> then weight \<Gamma> x - d_OUT g x else weight \<Gamma> x)"
    "vertex \<Gamma>' = vertex \<Gamma>"
    "web.more \<Gamma>' = web.more \<Gamma>"
    for x by(simp_all add: \<Gamma>'_def)
  have "countable_bipartite_web \<Gamma>'"
    by unfold_locales(simp_all add: A_in B_out A_vertex disjoint bipartite_V no_loop weight_outside currentD_outside_OUT[OF g]  currentD_weight_OUT[OF g] edge_antiparallel, rule bipartite_E)
  then interpret \<Gamma>': countable_bipartite_web \<Gamma>' .
  let ?u = "\<lambda>x. (d_IN g x - d_OUT g x) * indicator (- A \<Gamma>) x"

  have "hindered \<Gamma>'"
  proof(rule \<Gamma>'.hindered_reduce)
    show "?u x = 0" if "x \<notin> B \<Gamma>'" for x using that bipartite_V
      by(cases "vertex \<Gamma>' x")(auto simp add: currentD_outside_OUT[OF g] currentD_outside_IN[OF g])

    have *: "(\<Sum>\<^sup>+ x\<in>B \<Gamma>'. ?u x) = \<epsilon>" using disjoint
      by(auto intro!: nn_integral_cong simp add: \<epsilon>_def nn_integral_count_space_indicator currentD_outside_OUT[OF g] currentD_outside_IN[OF g] not_vertex split: split_indicator)
    thus "(\<Sum>\<^sup>+ x\<in>B \<Gamma>'. ?u x) \<noteq> \<top>" using \<epsilon>_finite by simp

    have **: "\<Gamma>'\<lparr>weight := weight \<Gamma>' - ?u\<rparr> = \<Gamma> \<ominus> g"
      using currentD_weight_IN[OF g] currentD_OUT_IN[OF g] currentD_IN[OF g] currentD_finite_OUT[OF g]
      by(intro web.equality)(simp_all add: fun_eq_iff diff_diff_ennreal' ennreal_diff_le_mono_left)
    show "hindered_by (\<Gamma>'\<lparr>weight := weight \<Gamma>' - ?u\<rparr>) (\<Sum>\<^sup>+ x\<in>B \<Gamma>'. ?u x)"
      unfolding * ** by(fact hindered)
    show "(\<lambda>x. (d_IN g x - d_OUT g x) * indicator (- A \<Gamma>) x) \<le> weight \<Gamma>'"
      using currentD_weight_IN[OF g]
      by (simp add: le_fun_def ennreal_diff_le_mono_left)
  qed
  then show ?thesis
    by(rule hindered_mono_web[rotated -1]) simp_all
qed

end

subsection \<open>Reduced weight in a loose web\<close>

definition reduce_weight :: "('v, 'more) web_scheme \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> ('v, 'more) web_scheme"
where "reduce_weight \<Gamma> x r = \<Gamma>\<lparr>weight := \<lambda>y. weight \<Gamma> y - (if x = y then r else 0)\<rparr>"

lemma reduce_weight_sel [simp]:
  "edge (reduce_weight \<Gamma> x r) = edge \<Gamma>"
  "A (reduce_weight \<Gamma> x r) = A \<Gamma>"
  "B (reduce_weight \<Gamma> x r) = B \<Gamma>"
  "vertex (reduce_weight \<Gamma> x r) = vertex \<Gamma>"
  "weight (reduce_weight \<Gamma> x r) y = (if x = y then weight \<Gamma> x - r else weight \<Gamma> y)"
  "web.more (reduce_weight \<Gamma> x r) = web.more \<Gamma>"
by(simp_all add: reduce_weight_def zero_ennreal_def[symmetric] vertex_def fun_eq_iff)

lemma essential_reduce_weight [simp]: "essential (reduce_weight \<Gamma> x r) = essential \<Gamma>"
by(simp add: fun_eq_iff essential_def)

lemma roofed_reduce_weight [simp]: "roofed_gen (reduce_weight \<Gamma> x r) = roofed_gen \<Gamma>"
by(simp add: fun_eq_iff roofed_def)

context countable_bipartite_web begin

context begin
private datatype (plugins del: transfer size) 'a vertex = SOURCE | SINK | Inner (inner: 'a)

private lemma notin_range_Inner:  "x \<notin> range Inner \<longleftrightarrow> x = SOURCE \<or> x = SINK"
by(cases x) auto

private lemma inj_Inner [simp]: "\<And>A. inj_on Inner A"
by(simp add: inj_on_def)

lemma unhinder_bipartite:
  assumes h: "\<And>n :: nat. current \<Gamma> (h n)"
  and SAT: "\<And>n. (B \<Gamma> \<inter> \<^bold>V) - {b} \<subseteq> SAT \<Gamma> (h n)"
  and b: "b \<in> B \<Gamma>"
  and IN: "(SUP n. d_IN (h n) b) = weight \<Gamma> b"
  and h0_b: "\<And>n. d_IN (h 0) b \<le> d_IN (h n) b"
  and b_V: "b \<in> \<^bold>V"
  shows "\<exists>h'. current \<Gamma> h' \<and> wave \<Gamma> h' \<and> B \<Gamma> \<inter> \<^bold>V \<subseteq> SAT \<Gamma> h'"
proof -
  write Inner ("\<langle>_\<rangle>")
  define edge'
    where "edge' xo yo =
      (case (xo, yo) of
        (\<langle>x\<rangle>, \<langle>y\<rangle>) \<Rightarrow> edge \<Gamma> x y \<or> edge \<Gamma> y x
      | (\<langle>x\<rangle>, SINK) \<Rightarrow> x \<in> A \<Gamma>
      | (SOURCE, \<langle>y\<rangle>) \<Rightarrow> y = b
      | (SINK, \<langle>x\<rangle>) \<Rightarrow> x \<in> A \<Gamma>
      | _ \<Rightarrow> False)" for xo yo
  have edge'_simps [simp]:
    "edge' \<langle>x\<rangle> \<langle>y\<rangle> \<longleftrightarrow> edge \<Gamma> x y \<or> edge \<Gamma> y x"
    "edge' \<langle>x\<rangle> SINK \<longleftrightarrow> x \<in> A \<Gamma>"
    "edge' SOURCE yo \<longleftrightarrow> yo = \<langle>b\<rangle>"
    "edge' SINK \<langle>x\<rangle> \<longleftrightarrow> x \<in> A \<Gamma>"
    "edge' SINK SINK \<longleftrightarrow> False"
    "edge' xo SOURCE \<longleftrightarrow> False"
    for x y yo xo by(simp_all add: edge'_def split: vertex.split)
  have edge'E: "thesis" if "edge' xo yo"
    "\<And>x y. \<lbrakk> xo = \<langle>x\<rangle>; yo = \<langle>y\<rangle>; edge \<Gamma> x y \<or> edge \<Gamma> y x \<rbrakk> \<Longrightarrow> thesis"
    "\<And>x. \<lbrakk> xo = \<langle>x\<rangle>; yo = SINK; x \<in> A \<Gamma> \<rbrakk> \<Longrightarrow> thesis"
    "\<And>x. \<lbrakk> xo = SOURCE; yo = \<langle>b\<rangle> \<rbrakk> \<Longrightarrow> thesis"
    "\<And>y. \<lbrakk> xo = SINK; yo = \<langle>y\<rangle>; y \<in> A \<Gamma> \<rbrakk> \<Longrightarrow> thesis"
    for xo yo thesis using that by(auto simp add: edge'_def split: option.split_asm vertex.split_asm)
  have edge'_Inner1 [elim!]: "thesis" if "edge' \<langle>x\<rangle> yo"
    "\<And>y. \<lbrakk> yo = \<langle>y\<rangle>; edge \<Gamma> x y \<or> edge \<Gamma> y x \<rbrakk> \<Longrightarrow> thesis"
    "\<lbrakk> yo = SINK; x \<in> A \<Gamma> \<rbrakk> \<Longrightarrow> thesis"
    for x yo thesis using that by(auto elim: edge'E)
  have edge'_Inner2 [elim!]: "thesis" if "edge' xo \<langle>y\<rangle>"
    "\<And>x. \<lbrakk> xo = \<langle>x\<rangle>; edge \<Gamma> x y \<or> edge \<Gamma> y x \<rbrakk> \<Longrightarrow> thesis"
    "\<lbrakk> xo = SOURCE; y = b \<rbrakk> \<Longrightarrow> thesis"
    "\<lbrakk> xo = SINK; y \<in> A \<Gamma> \<rbrakk> \<Longrightarrow> thesis"
    for xo y thesis using that by(auto elim: edge'E)
  have edge'_SINK1 [elim!]: "thesis" if "edge' SINK yo"
    "\<And>y. \<lbrakk> yo = \<langle>y\<rangle>; y \<in> A \<Gamma> \<rbrakk> \<Longrightarrow> thesis"
    for yo thesis using that by(auto elim: edge'E)
  have edge'_SINK2 [elim!]: "thesis" if "edge' xo SINK"
    "\<And>x. \<lbrakk> xo = \<langle>x\<rangle>; x \<in> A \<Gamma> \<rbrakk> \<Longrightarrow> thesis"
    for xo thesis using that by(auto elim: edge'E)

  define cap
    where "cap xoyo =
      (case xoyo of
        (\<langle>x\<rangle>, \<langle>y\<rangle>) \<Rightarrow> if edge \<Gamma> x y then h 0 (x, y) else if edge \<Gamma> y x then max (weight \<Gamma> x) (weight \<Gamma> y) else 0
      | (\<langle>x\<rangle>, SINK) \<Rightarrow> if x \<in> A \<Gamma> then weight \<Gamma> x - d_OUT (h 0) x else 0
      | (SOURCE, yo) \<Rightarrow> if yo = \<langle>b\<rangle> then weight \<Gamma> b - d_IN (h 0) b else 0
      | (SINK, \<langle>y\<rangle>) \<Rightarrow> if y \<in> A \<Gamma> then weight \<Gamma> y else 0
      | _ \<Rightarrow> 0)" for xoyo
  have cap_simps [simp]:
    "cap (\<langle>x\<rangle>, \<langle>y\<rangle>) = (if edge \<Gamma> x y then h 0 (x, y) else if edge \<Gamma> y x then max (weight \<Gamma> x) (weight \<Gamma> y) else 0)"
    "cap (\<langle>x\<rangle>, SINK) = (if x \<in> A \<Gamma> then weight \<Gamma> x - d_OUT (h 0) x else 0)"
    "cap (SOURCE, yo) = (if yo = \<langle>b\<rangle> then weight \<Gamma> b - d_IN (h 0) b else 0)"
    "cap (SINK, \<langle>y\<rangle>) = (if y \<in> A \<Gamma> then weight \<Gamma> y else 0)"
    "cap (SINK, SINK) = 0"
    "cap (xo, SOURCE) = 0"
    for x y yo xo by(simp_all add: cap_def split: vertex.split)
  define \<Psi> where "\<Psi> = \<lparr>edge = edge', capacity = cap, source = SOURCE, sink = SINK\<rparr>"
  have \<Psi>_sel [simp]:
    "edge \<Psi> = edge'"
    "capacity \<Psi> = cap"
    "source \<Psi> = SOURCE"
    "sink \<Psi> = SINK"
    by(simp_all add: \<Psi>_def)

  have cap_outside1: "\<not> vertex \<Gamma> x \<Longrightarrow> cap (\<langle>x\<rangle>, y) = 0" for x y using A_vertex
    by(cases y)(auto simp add: vertex_def)
  have capacity_A_weight: "d_OUT cap \<langle>x\<rangle> \<le> 2 * weight \<Gamma> x" if "x \<in> A \<Gamma>" for x
  proof -
    have "d_OUT cap \<langle>x\<rangle> \<le> (\<Sum>\<^sup>+ y. h 0 (x, inner y) * indicator (range Inner) y + weight \<Gamma> x * indicator {SINK} y)"
      using that disjoint unfolding d_OUT_def
      by(auto intro!: nn_integral_mono diff_le_self_ennreal simp add: A_in notin_range_Inner  split: split_indicator)
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>range Inner. h 0 (x, inner y)) + weight \<Gamma> x"
      by(auto simp add: nn_integral_count_space_indicator nn_integral_add)
    also have "(\<Sum>\<^sup>+ y\<in>range Inner. h 0 (x, inner y)) = d_OUT (h 0) x"
      by(simp add: d_OUT_def nn_integral_count_space_reindex)
    also have "\<dots> \<le> weight \<Gamma> x" using h by(rule currentD_weight_OUT)
    finally show ?thesis unfolding one_add_one[symmetric] distrib_right by(simp add: add_right_mono)
  qed
  have flow_attainability: "flow_attainability \<Psi>"
  proof
    have "\<^bold>E\<^bsub>\<Psi>\<^esub> \<subseteq> (\<lambda>(x, y). (\<langle>x\<rangle>, \<langle>y\<rangle>)) ` \<^bold>E \<union> (\<lambda>(x, y). (\<langle>y\<rangle>, \<langle>x\<rangle>)) ` \<^bold>E \<union> (\<lambda>x. (\<langle>x\<rangle>, SINK)) ` A \<Gamma> \<union> (\<lambda>x. (SINK, \<langle>x\<rangle>)) ` A \<Gamma> \<union> {(SOURCE, \<langle>b\<rangle>)}"
      by(auto simp add: edge'_def split: vertex.split_asm)
    moreover have "countable (A \<Gamma>)" using A_vertex by(rule countable_subset) simp
    ultimately show "countable \<^bold>E\<^bsub>\<Psi>\<^esub>" by(auto elim: countable_subset)
  next
    fix v
    assume "v \<noteq> sink \<Psi>"
    then consider (source) "v = SOURCE" | (A) x where "v = \<langle>x\<rangle>" "x \<in> A \<Gamma>"
      | (B) y where "v = \<langle>y\<rangle>" "y \<notin> A \<Gamma>" "y \<in> \<^bold>V" | (outside) x where "v = \<langle>x\<rangle>" "x \<notin> \<^bold>V"
      by(cases v) auto
    then show "d_IN (capacity \<Psi>) v \<noteq> \<top> \<or> d_OUT (capacity \<Psi>) v \<noteq> \<top>"
    proof cases
      case source thus ?thesis by(simp add: d_IN_def)
    next
      case (A x)
      thus ?thesis using capacity_A_weight[of x] by (auto simp: top_unique ennreal_mult_eq_top_iff)
    next
      case (B y)
      have "d_IN (capacity \<Psi>) v \<le> (\<Sum>\<^sup>+ x. h 0 (inner x, y) * indicator (range Inner) x + weight \<Gamma> b * indicator {SOURCE} x)"
        using B bipartite_V
        by(auto 4 4 intro!: nn_integral_mono simp add: diff_le_self_ennreal   d_IN_def notin_range_Inner nn_integral_count_space_indicator currentD_outside[OF h] split: split_indicator dest: bipartite_E)
      also have "\<dots> = (\<Sum>\<^sup>+ x\<in>range Inner. h 0 (inner x, y)) + weight \<Gamma> b"
        by(simp add: nn_integral_add nn_integral_count_space_indicator)
      also have "(\<Sum>\<^sup>+ x\<in>range Inner. h 0 (inner x, y)) = d_IN (h 0) y"
        by(simp add: d_IN_def nn_integral_count_space_reindex)
      also have "d_IN (h 0) y \<le> weight \<Gamma> y" using h by(rule currentD_weight_IN)
      finally show ?thesis by(auto simp add: top_unique add_right_mono split: if_split_asm)
    next
      case outside
      hence "d_OUT (capacity \<Psi>) v = 0" using A_vertex
        by(auto simp add: d_OUT_def nn_integral_0_iff_AE AE_count_space cap_def vertex_def split: vertex.split)
      thus ?thesis by simp
    qed
  next
    show "capacity \<Psi> e \<noteq> \<top>" for e
      by(auto simp add: cap_def max_def vertex_def currentD_finite[OF h] split: vertex.split prod.split)
    show "capacity \<Psi> e = 0" if "e \<notin> \<^bold>E\<^bsub>\<Psi>\<^esub>" for e using that
      by(auto simp add: cap_def max_def split: prod.split; split vertex.split)+
    show "\<not> edge \<Psi> x (source \<Psi>)" for x using b by(auto simp add: B_out)
    show "\<not> edge \<Psi> x x" for x by(cases x)(simp_all add: no_loop)
    show "source \<Psi> \<noteq> sink \<Psi>" by simp
  qed
  then interpret \<Psi>: flow_attainability "\<Psi>" .
  define \<alpha> where "\<alpha> = (SUP f\<in>{f. flow \<Psi> f}. value_flow \<Psi> f)"

  define f
    where "f n xoyo =
    (case xoyo of
      (\<langle>x\<rangle>, \<langle>y\<rangle>) \<Rightarrow> if edge \<Gamma> x y then h 0 (x, y) - h n (x, y) else if edge \<Gamma> y x then h n (y, x) - h 0 (y, x) else 0
    | (SOURCE, \<langle>y\<rangle>) \<Rightarrow> if y = b then d_IN (h n) b - d_IN (h 0) b else 0
    | (\<langle>x\<rangle>, SINK) \<Rightarrow> if x \<in> A \<Gamma> then d_OUT (h n) x - d_OUT (h 0) x else 0
    | (SINK, \<langle>y\<rangle>) \<Rightarrow> if y \<in> A \<Gamma> then d_OUT (h 0) y - d_OUT (h n) y else 0
    | _ \<Rightarrow> 0)" for n xoyo
  have f_cases: thesis if "\<And>x y. e = (\<langle>x\<rangle>, \<langle>y\<rangle>) \<Longrightarrow> thesis" "\<And>y. e = (SOURCE, \<langle>y\<rangle>) \<Longrightarrow> thesis"
    "\<And>x. e = (\<langle>x\<rangle>, SINK) \<Longrightarrow> thesis" "\<And>y. e = (SINK, \<langle>y\<rangle>) \<Longrightarrow> thesis" "e = (SINK, SINK) \<Longrightarrow> thesis"
    "\<And>xo. e = (xo, SOURCE) \<Longrightarrow> thesis" "e = (SOURCE, SINK) \<Longrightarrow> thesis"
    for e :: "'v vertex edge" and thesis
    using that by(cases e; cases "fst e" "snd e" rule: vertex.exhaust[case_product vertex.exhaust]) simp_all
  have f_simps [simp]:
    "f n (\<langle>x\<rangle>, \<langle>y\<rangle>) = (if edge \<Gamma> x y then h 0 (x, y) - h n (x, y) else if edge \<Gamma> y x then h n (y, x) - h 0 (y, x) else 0)"
    "f n (SOURCE, \<langle>y\<rangle>) = (if y = b then d_IN (h n) b - d_IN (h 0) b else 0)"
    "f n (\<langle>x\<rangle>, SINK) = (if x \<in> A \<Gamma> then d_OUT (h n) x - d_OUT (h 0) x else 0)"
    "f n (SINK, \<langle>y\<rangle>) = (if y \<in> A \<Gamma> then d_OUT (h 0) y - d_OUT (h n) y else 0)"
    "f n (SOURCE, SINK) = 0"
    "f n (SINK, SINK) = 0"
    "f n (xo, SOURCE) = 0"
    for n x y xo by(simp_all add: f_def split: vertex.split)
  have OUT_f_SOURCE: "d_OUT (f n) SOURCE = d_IN (h n) b - d_IN (h 0) b" for n
  proof(rule trans)
    show "d_OUT (f n) SOURCE = (\<Sum>\<^sup>+ y. f n (SOURCE, y) * indicator {\<langle>b\<rangle>} y)" unfolding d_OUT_def
      apply(rule nn_integral_cong) subgoal for x by(cases x) auto done
    show "\<dots> = d_IN (h n) b - d_IN (h 0) b" using h0_b[of n]
      by(auto simp add: max_def)
  qed

  have OUT_f_outside: "d_OUT (f n) \<langle>x\<rangle> = 0" if "x \<notin> \<^bold>V" for x n using A_vertex that
    apply(clarsimp simp add: d_OUT_def nn_integral_0_iff emeasure_count_space_eq_0)
    subgoal for y by(cases y)(auto simp add: vertex_def)
    done
  have IN_f_outside: "d_IN (f n) \<langle>x\<rangle> = 0" if "x \<notin> \<^bold>V" for x n using b_V that
    apply(clarsimp simp add: d_IN_def nn_integral_0_iff emeasure_count_space_eq_0)
    subgoal for y by(cases y)(auto simp add: currentD_outside_OUT[OF h] vertex_def)
    done

  have f: "flow \<Psi> (f n)" for n
  proof
    show f_le: "f n e \<le> capacity \<Psi> e" for e
      using currentD_weight_out[OF h] currentD_weight_IN[OF h] currentD_weight_OUT[OF h]
      by(cases e rule: f_cases)
        (auto dest: edge_antiparallel simp add: not_le le_max_iff_disj intro: ennreal_minus_mono ennreal_diff_le_mono_left)

    fix xo
    assume "xo \<noteq> source \<Psi>" "xo \<noteq> sink \<Psi>"
    then consider (A) x where "xo = \<langle>x\<rangle>" "x \<in> A \<Gamma>" | (B) x where "xo = \<langle>x\<rangle>" "x \<in> B \<Gamma>" "x \<in> \<^bold>V"
      | (outside) x where "xo = \<langle>x\<rangle>" "x \<notin> \<^bold>V" using bipartite_V by(cases xo) auto
    then show "KIR (f n) xo"
    proof cases
      case outside
      thus ?thesis by(simp add: OUT_f_outside IN_f_outside)
    next
      case A

      have finite1: "(\<Sum>\<^sup>+ y. h n (x, y) * indicator A y) \<noteq> \<top>" for A n
        using currentD_finite_OUT[OF h, of n x, unfolded d_OUT_def]
        by(rule neq_top_trans)(auto intro!: nn_integral_mono simp add: split: split_indicator)

      let ?h0_ge_hn = "{y. h 0 (x, y) \<ge> h n (x, y)}"
      let ?h0_lt_hn = "{y. h 0 (x, y) < h n (x, y)}"

      have "d_OUT (f n) \<langle>x\<rangle> = (\<Sum>\<^sup>+ y. f n (\<langle>x\<rangle>, y) * indicator (range Inner) y + f n (\<langle>x\<rangle>, y) * indicator {SINK} y)"
        unfolding d_OUT_def by(intro nn_integral_cong)(auto split: split_indicator simp add: notin_range_Inner)
      also have "\<dots> = (\<Sum>\<^sup>+ y\<in>range Inner. f n (\<langle>x\<rangle>, y)) + f n (\<langle>x\<rangle>, SINK)"
        by(simp add: nn_integral_add nn_integral_count_space_indicator max.left_commute max.commute)
      also have "(\<Sum>\<^sup>+ y\<in>range Inner. f n (\<langle>x\<rangle>, y)) = (\<Sum>\<^sup>+ y. h 0 (x, y) - h n (x, y))" using A
        apply(simp add: nn_integral_count_space_reindex cong: nn_integral_cong_simp outgoing_def)
        apply(auto simp add: nn_integral_count_space_indicator outgoing_def A_in max.absorb1 currentD_outside[OF h] intro!: nn_integral_cong split: split_indicator dest: edge_antiparallel)
        done
      also have "\<dots> = (\<Sum>\<^sup>+ y. h 0 (x, y) * indicator ?h0_ge_hn y) - (\<Sum>\<^sup>+ y. h n (x, y) * indicator ?h0_ge_hn y)"
        apply(subst nn_integral_diff[symmetric])
        apply(simp_all add: AE_count_space finite1 split: split_indicator)
        apply(rule nn_integral_cong; auto simp add: max_def not_le split: split_indicator)
        by (metis diff_eq_0_ennreal le_less not_le top_greatest)
      also have "(\<Sum>\<^sup>+ y. h n (x, y) * indicator ?h0_ge_hn y) = d_OUT (h n) x - (\<Sum>\<^sup>+ y. h n (x, y) * indicator ?h0_lt_hn y)"
        unfolding d_OUT_def
        apply(subst nn_integral_diff[symmetric])
        apply(auto simp add: AE_count_space finite1 currentD_finite[OF h] split: split_indicator intro!: nn_integral_cong)
        done
      also have "(\<Sum>\<^sup>+ y. h 0 (x, y) * indicator ?h0_ge_hn y) - \<dots> + f n (\<langle>x\<rangle>, SINK) =
        (\<Sum>\<^sup>+ y. h 0 (x, y) * indicator ?h0_ge_hn y) + (\<Sum>\<^sup>+ y. h n (x, y) * indicator ?h0_lt_hn y) - min (d_OUT (h n) x) (d_OUT (h 0) x)"
        using finite1[of n "{_}"] A finite1[of n UNIV]
        apply (subst diff_diff_ennreal')
        apply (auto simp: d_OUT_def finite1 AE_count_space nn_integral_diff[symmetric] top_unique nn_integral_add[symmetric]
                    split: split_indicator intro!: nn_integral_mono ennreal_diff_self)
        apply (simp add: min_def not_le diff_eq_0_ennreal finite1 less_top[symmetric])
        apply (subst diff_add_assoc2_ennreal)
        apply (auto simp: add_diff_eq_ennreal intro!: nn_integral_mono split: split_indicator)
        apply (subst diff_diff_commute_ennreal)
        apply (simp add: ennreal_add_diff_cancel )
        done
      also have "\<dots> = (\<Sum>\<^sup>+ y. h n (x, y) * indicator ?h0_lt_hn y) - (d_OUT (h 0) x - (\<Sum>\<^sup>+ y. h 0 (x, y) * indicator ?h0_ge_hn y)) + f n (SINK, \<langle>x\<rangle>)"
        apply(rule sym)
        using finite1[of 0 "{_}"] A finite1[of 0 UNIV]
        apply (subst diff_diff_ennreal')
        apply (auto simp: d_OUT_def finite1 AE_count_space nn_integral_diff[symmetric] top_unique nn_integral_add[symmetric]
                    split: split_indicator intro!: nn_integral_mono ennreal_diff_self)
        apply (simp add: min_def not_le diff_eq_0_ennreal finite1 less_top[symmetric])
        apply (subst diff_add_assoc2_ennreal)
        apply (auto simp: add_diff_eq_ennreal intro!: nn_integral_mono split: split_indicator)
        apply (subst diff_diff_commute_ennreal)
        apply (simp_all add: ennreal_add_diff_cancel ac_simps)
        done
      also have "d_OUT (h 0) x - (\<Sum>\<^sup>+ y. h 0 (x, y) * indicator ?h0_ge_hn y) = (\<Sum>\<^sup>+ y. h 0 (x, y) * indicator ?h0_lt_hn y)"
        unfolding d_OUT_def
        apply(subst nn_integral_diff[symmetric])
        apply(auto simp add: AE_count_space finite1 currentD_finite[OF h] split: split_indicator intro!: nn_integral_cong)
        done
      also have "(\<Sum>\<^sup>+ y. h n (x, y) * indicator ?h0_lt_hn y) - \<dots> = (\<Sum>\<^sup>+ y. h n (x, y) - h 0 (x, y))"
        apply(subst nn_integral_diff[symmetric])
        apply(simp_all add: AE_count_space finite1 order.strict_implies_order split: split_indicator)
        apply(rule nn_integral_cong; auto simp add: currentD_finite[OF h] top_unique less_top[symmetric] not_less split: split_indicator intro!: diff_eq_0_ennreal)
        done
      also have "\<dots> = (\<Sum>\<^sup>+ y\<in>range Inner. f n (y, \<langle>x\<rangle>))" using A
        apply(simp add: nn_integral_count_space_reindex cong: nn_integral_cong_simp outgoing_def)
        apply(auto simp add: nn_integral_count_space_indicator outgoing_def A_in max.commute currentD_outside[OF h] intro!: nn_integral_cong split: split_indicator dest: edge_antiparallel)
        done
      also have "\<dots> + f n (SINK, \<langle>x\<rangle>) = (\<Sum>\<^sup>+ y. f n (y, \<langle>x\<rangle>) * indicator (range Inner) y + f n (y, \<langle>x\<rangle>) * indicator {SINK} y)"
        by(simp add: nn_integral_add nn_integral_count_space_indicator)
      also have "\<dots> = d_IN (f n) \<langle>x\<rangle>"
        using A b disjoint unfolding d_IN_def
        by(intro nn_integral_cong)(auto split: split_indicator simp add: notin_range_Inner)
      finally show ?thesis using A by simp
    next
      case (B x)

      have finite1: "(\<Sum>\<^sup>+ y. h n (y, x) * indicator A y) \<noteq> \<top>" for A n
        using currentD_finite_IN[OF h, of n x, unfolded d_IN_def]
        by(rule neq_top_trans)(auto intro!: nn_integral_mono split: split_indicator)

      have finite_h[simp]: "h n (y, x) < \<top>" for y n
        using finite1[of n "{y}"] by (simp add: less_top)

      let ?h0_gt_hn = "{y. h 0 (y, x) > h n (y, x)}"
      let ?h0_le_hn = "{y. h 0 (y, x) \<le> h n (y, x)}"

      have eq: "d_IN (h 0) x + f n (SOURCE, \<langle>x\<rangle>) = d_IN (h n) x"
      proof(cases "x = b")
        case True with currentD_finite_IN[OF h, of _ b] show ?thesis
          by(simp add: add_diff_self_ennreal h0_b)
      next
        case False
        with B SAT have "x \<in> SAT \<Gamma> (h n)" "x \<in> SAT \<Gamma> (h 0)" by auto
        with B disjoint have "d_IN (h n) x = d_IN (h 0) x" by(auto simp add: currentD_SAT[OF h])
        thus ?thesis using False by(simp add: currentD_finite_IN[OF h])
      qed

      have "d_IN (f n) \<langle>x\<rangle> = (\<Sum>\<^sup>+ y. f n (y, \<langle>x\<rangle>) * indicator (range Inner) y + f n (y, \<langle>x\<rangle>) * indicator {SOURCE} y)"
        using B disjoint unfolding d_IN_def
        by(intro nn_integral_cong)(auto split: split_indicator simp add: notin_range_Inner)
      also have "\<dots> = (\<Sum>\<^sup>+ y\<in>range Inner. f n (y, \<langle>x\<rangle>)) + f n (SOURCE, \<langle>x\<rangle>)" using h0_b[of n]
        by(simp add: nn_integral_add nn_integral_count_space_indicator max_def)
      also have "(\<Sum>\<^sup>+ y\<in>range Inner. f n (y, \<langle>x\<rangle>)) = (\<Sum>\<^sup>+ y. h 0 (y, x) - h n (y, x))"
        using B disjoint
        apply(simp add: nn_integral_count_space_reindex cong: nn_integral_cong_simp outgoing_def)
        apply(auto simp add: nn_integral_count_space_indicator outgoing_def B_out max.commute currentD_outside[OF h] intro!: nn_integral_cong split: split_indicator dest: edge_antiparallel)
        done
      also have "\<dots> = (\<Sum>\<^sup>+ y. h 0 (y, x) * indicator ?h0_gt_hn y) - (\<Sum>\<^sup>+ y. h n (y, x) * indicator ?h0_gt_hn y)"
        apply(subst nn_integral_diff[symmetric])
        apply(simp_all add: AE_count_space finite1 order.strict_implies_order split: split_indicator)
        apply(rule nn_integral_cong; auto simp add: currentD_finite[OF h] top_unique less_top[symmetric] not_less split: split_indicator intro!: diff_eq_0_ennreal)
        done
      also have eq_h_0: "(\<Sum>\<^sup>+ y. h 0 (y, x) * indicator ?h0_gt_hn y) = d_IN (h 0) x - (\<Sum>\<^sup>+ y. h 0 (y, x) * indicator ?h0_le_hn y)"
        unfolding d_IN_def
        apply(subst nn_integral_diff[symmetric])
        apply(auto simp add: AE_count_space finite1 currentD_finite[OF h] split: split_indicator intro!: nn_integral_cong)
        done
      also have eq_h_n: "(\<Sum>\<^sup>+ y. h n (y, x) * indicator ?h0_gt_hn y) = d_IN (h n) x - (\<Sum>\<^sup>+ y. h n (y, x) * indicator ?h0_le_hn y)"
        unfolding d_IN_def
        apply(subst nn_integral_diff[symmetric])
        apply(auto simp add: AE_count_space finite1 currentD_finite[OF h] split: split_indicator intro!: nn_integral_cong)
        done
      also have "d_IN (h 0) x - (\<Sum>\<^sup>+ y. h 0 (y, x) * indicator ?h0_le_hn y) - (d_IN (h n) x - (\<Sum>\<^sup>+ y. h n (y, x) * indicator ?h0_le_hn y)) + f n (SOURCE, \<langle>x\<rangle>) =
                (\<Sum>\<^sup>+ y. h n (y, x) * indicator ?h0_le_hn y) - (\<Sum>\<^sup>+ y. h 0 (y, x) * indicator ?h0_le_hn y)"
        apply (subst diff_add_assoc2_ennreal)
        subgoal by (auto simp add: eq_h_0[symmetric] eq_h_n[symmetric] split: split_indicator intro!: nn_integral_mono)
        apply (subst diff_add_assoc2_ennreal)
        subgoal by (auto simp: d_IN_def split: split_indicator intro!: nn_integral_mono)
        apply (subst diff_diff_commute_ennreal)
        apply (subst diff_diff_ennreal')
        subgoal
          by (auto simp: d_IN_def split: split_indicator intro!: nn_integral_mono) []
        subgoal
          unfolding eq_h_n[symmetric]
          by (rule add_increasing2)
             (auto simp add: d_IN_def split: split_indicator intro!: nn_integral_mono)
        apply (subst diff_add_assoc2_ennreal[symmetric])
        unfolding eq
        using currentD_finite_IN[OF h]
        apply simp_all
        done
      also have "(\<Sum>\<^sup>+ y. h n (y, x) * indicator ?h0_le_hn y) - (\<Sum>\<^sup>+ y. h 0 (y, x) * indicator ?h0_le_hn y) = (\<Sum>\<^sup>+ y. h n (y, x) - h 0 (y, x))"
        apply(subst nn_integral_diff[symmetric])
        apply(simp_all add: AE_count_space max_def finite1 split: split_indicator)
        apply(rule nn_integral_cong; auto simp add: not_le split: split_indicator)
        by (metis diff_eq_0_ennreal le_less not_le top_greatest)
      also have "\<dots> = (\<Sum>\<^sup>+ y\<in>range Inner. f n (\<langle>x\<rangle>, y))" using B disjoint
        apply(simp add: nn_integral_count_space_reindex cong: nn_integral_cong_simp outgoing_def)
        apply(auto simp add: B_out currentD_outside[OF h] max.commute intro!: nn_integral_cong split: split_indicator dest: edge_antiparallel)
        done
      also have "\<dots> = (\<Sum>\<^sup>+ y. f n (\<langle>x\<rangle>, y) * indicator (range Inner) y)"
        by(simp add: nn_integral_add nn_integral_count_space_indicator max.left_commute max.commute)
      also have "\<dots> = d_OUT (f n) \<langle>x\<rangle>"  using B disjoint
        unfolding d_OUT_def by(intro nn_integral_cong)(auto split: split_indicator simp add: notin_range_Inner)
      finally show ?thesis using B by(simp)
    qed
  qed

  have "weight \<Gamma> b - d_IN (h 0) b = (SUP n. value_flow \<Psi> (f n))"
    using OUT_f_SOURCE currentD_finite_IN[OF h, of 0 b] IN
    by (simp add: SUP_diff_ennreal less_top)
  also have "(SUP n. value_flow \<Psi> (f n)) \<le> \<alpha>" unfolding \<alpha>_def
    apply(rule SUP_least)
    apply(rule SUP_upper)
    apply(simp add: f)
    done
  also have "\<alpha> \<le> weight \<Gamma> b - d_IN (h 0) b" unfolding \<alpha>_def
  proof(rule SUP_least; clarsimp)
    fix f
    assume f: "flow \<Psi> f"
    have "d_OUT f SOURCE = (\<Sum>\<^sup>+ y. f (SOURCE, y) * indicator {\<langle>b\<rangle>} y)" unfolding d_OUT_def
      apply(rule nn_integral_cong)
      subgoal for x using flowD_capacity[OF f, of "(SOURCE, x)"]
        by(auto split: split_indicator)
      done
    also have "\<dots> = f (SOURCE, \<langle>b\<rangle>)" by(simp add: max_def)
    also have "\<dots> \<le> weight \<Gamma> b - d_IN (h 0) b" using flowD_capacity[OF f, of "(SOURCE, \<langle>b\<rangle>)"] by simp
    finally show "d_OUT f SOURCE \<le> \<dots>" .
  qed
  ultimately have \<alpha>: "\<alpha> = weight \<Gamma> b - d_IN (h 0) b" by(rule antisym[rotated])
  hence \<alpha>_finite: "\<alpha> \<noteq> \<top>" by simp

  from \<Psi>.ex_max_flow
  obtain g where g: "flow \<Psi> g"
    and value_g: "value_flow \<Psi> g = \<alpha>"
    and IN_g: "\<And>x. d_IN g x \<le> value_flow \<Psi> g" unfolding \<alpha>_def by blast

  have g_le_h0: "g (\<langle>x\<rangle>, \<langle>y\<rangle>) \<le> h 0 (x, y)" if "edge \<Gamma> x y" for x y
    using flowD_capacity[OF g, of "(\<langle>x\<rangle>, \<langle>y\<rangle>)"] that by simp
  note [simp] = \<Psi>.flowD_finite[OF g]

  have g_SOURCE: "g (SOURCE, \<langle>x\<rangle>) = (if x = b then \<alpha> else 0)" for x
  proof(cases "x = b")
    case True
    have "g (SOURCE, \<langle>x\<rangle>) = (\<Sum>\<^sup>+ y. g (SOURCE, y) * indicator {\<langle>x\<rangle>} y)" by(simp add: max_def)
    also have "\<dots> = value_flow \<Psi> g" unfolding d_OUT_def using True
      by(intro nn_integral_cong)(auto split: split_indicator intro: \<Psi>.flowD_outside[OF g])
    finally show ?thesis using value_g by(simp add: True)
  qed(simp add: \<Psi>.flowD_outside[OF g])

  let ?g = "\<lambda>(x, y). g (\<langle>y\<rangle>, \<langle>x\<rangle>)"

  define h' where "h' = h 0 \<oplus> ?g"
  have h'_simps: "h' (x, y) = (if edge \<Gamma> x y then h 0 (x, y) + g (\<langle>y\<rangle>, \<langle>x\<rangle>) - g (\<langle>x\<rangle>, \<langle>y\<rangle>) else 0)" for x y
    by(simp add: h'_def)

  have OUT_h'_B [simp]: "d_OUT h' x = 0" if "x \<in> B \<Gamma>" for x using that unfolding d_OUT_def
    by(simp add: nn_integral_0_iff emeasure_count_space_eq_0)(simp add: h'_simps B_out)
  have IN_h'_A [simp]: "d_IN h' x = 0" if "x \<in> A \<Gamma>" for x using that unfolding d_IN_def
    by(simp add: nn_integral_0_iff emeasure_count_space_eq_0)(simp add: h'_simps A_in)
  have h'_outside: "h' e = 0" if "e \<notin> \<^bold>E" for e unfolding h'_def using that by(rule plus_flow_outside)
  have OUT_h'_outside: "d_OUT h' x = 0" and IN_h'_outside: "d_IN h' x = 0" if "x \<notin> \<^bold>V" for x using that
    by(auto simp add: d_OUT_def d_IN_def nn_integral_0_iff emeasure_count_space_eq_0 vertex_def intro: h'_outside)

  have g_le_OUT: "g (SINK, \<langle>x\<rangle>) \<le> d_OUT g \<langle>x\<rangle>" for x
    by (subst flowD_KIR[OF g]) (simp_all add: d_IN_ge_point)

  have OUT_g_A: "d_OUT ?g x = d_OUT g \<langle>x\<rangle> - g (SINK, \<langle>x\<rangle>)" if "x \<in> A \<Gamma>" for x
  proof -
    have "d_OUT ?g x = (\<Sum>\<^sup>+ y\<in>range Inner. g (y, \<langle>x\<rangle>))"
      by(simp add: nn_integral_count_space_reindex d_OUT_def)
    also have "\<dots> = d_IN g \<langle>x\<rangle> - (\<Sum>\<^sup>+ y. g (y, \<langle>x\<rangle>) * indicator {SINK} y)" unfolding d_IN_def
      using that b disjoint flowD_capacity[OF g, of "(SOURCE, \<langle>x\<rangle>)"]
      by(subst nn_integral_diff[symmetric])
        (auto simp add: nn_integral_count_space_indicator notin_range_Inner max_def intro!: nn_integral_cong split: split_indicator if_split_asm)
    also have "\<dots> = d_OUT g \<langle>x\<rangle> - g (SINK, \<langle>x\<rangle>)" by(simp add: flowD_KIR[OF g] max_def)
    finally show ?thesis .
  qed
  have IN_g_A: "d_IN ?g x = d_OUT g \<langle>x\<rangle> - g (\<langle>x\<rangle>, SINK)" if "x \<in> A \<Gamma>" for x
  proof -
    have "d_IN ?g x = (\<Sum>\<^sup>+ y\<in>range Inner. g (\<langle>x\<rangle>, y))"
      by(simp add: nn_integral_count_space_reindex d_IN_def)
    also have "\<dots> = d_OUT g \<langle>x\<rangle> - (\<Sum>\<^sup>+ y. g (\<langle>x\<rangle>, y) * indicator {SINK} y)" unfolding d_OUT_def
      using that b disjoint flowD_capacity[OF g, of "(\<langle>x\<rangle>, SOURCE)"]
      by(subst nn_integral_diff[symmetric])
        (auto simp add: nn_integral_count_space_indicator notin_range_Inner max_def intro!: nn_integral_cong split: split_indicator if_split_asm)
    also have "\<dots> = d_OUT g \<langle>x\<rangle> - g (\<langle>x\<rangle>, SINK)" by(simp add: max_def)
    finally show ?thesis .
  qed
  have OUT_g_B: "d_OUT ?g x = d_IN g \<langle>x\<rangle> - g (SOURCE, \<langle>x\<rangle>)" if "x \<in> B \<Gamma>" for x
  proof -
    have "d_OUT ?g x = (\<Sum>\<^sup>+ y\<in>range Inner. g (y, \<langle>x\<rangle>))"
      by(simp add: nn_integral_count_space_reindex d_OUT_def)
    also have "\<dots> = d_IN g \<langle>x\<rangle> - (\<Sum>\<^sup>+ y. g (y, \<langle>x\<rangle>) * indicator {SOURCE} y)" unfolding d_IN_def
      using that b disjoint flowD_capacity[OF g, of "(SINK, \<langle>x\<rangle>)"]
      by(subst nn_integral_diff[symmetric])
        (auto simp add: nn_integral_count_space_indicator notin_range_Inner max_def intro!: nn_integral_cong split: split_indicator if_split_asm)
    also have "\<dots> = d_IN g \<langle>x\<rangle> - g (SOURCE, \<langle>x\<rangle>)" by(simp add: max_def)
    finally show ?thesis .
  qed
  have IN_g_B: "d_IN ?g x = d_OUT g \<langle>x\<rangle>" if "x \<in> B \<Gamma>" for x
  proof -
    have "d_IN ?g x = (\<Sum>\<^sup>+ y\<in>range Inner. g (\<langle>x\<rangle>, y))"
      by(simp add: nn_integral_count_space_reindex d_IN_def)
    also have "\<dots> = d_OUT g \<langle>x\<rangle>" unfolding d_OUT_def using that disjoint
      by(auto 4 3 simp add: nn_integral_count_space_indicator notin_range_Inner intro!: nn_integral_cong \<Psi>.flowD_outside[OF g] split: split_indicator)
    finally show ?thesis .
  qed

  have finite_g_IN: "d_IN ?g x \<noteq> \<top>" for x using \<alpha>_finite
  proof(rule neq_top_trans)
    have "d_IN ?g x = (\<Sum>\<^sup>+ y\<in>range Inner. g (\<langle>x\<rangle>, y))"
      by(auto simp add: d_IN_def nn_integral_count_space_reindex)
    also have "\<dots> \<le> d_OUT g \<langle>x\<rangle>" unfolding d_OUT_def
      by(auto simp add: nn_integral_count_space_indicator intro!: nn_integral_mono split: split_indicator)
    also have "\<dots> = d_IN g \<langle>x\<rangle>" by(rule flowD_KIR[OF g]) simp_all
    also have "\<dots> \<le> \<alpha>" using IN_g value_g by simp
    finally show "d_IN ?g x \<le> \<alpha>" .
  qed

  have OUT_h'_A: "d_OUT h' x = d_OUT (h 0) x + g (\<langle>x\<rangle>, SINK) - g (SINK, \<langle>x\<rangle>)" if "x \<in> A \<Gamma>" for x
  proof -
    have "d_OUT h' x = d_OUT (h 0) x + (\<Sum>\<^sup>+ y. ?g (x, y) * indicator \<^bold>E (x, y)) - (\<Sum>\<^sup>+ y. ?g (y, x) * indicator \<^bold>E (x, y))"
      unfolding h'_def
      apply(subst OUT_plus_flow[of \<Gamma> "h 0" ?g, OF currentD_outside'[OF h]])
      apply(auto simp add: g_le_h0 finite_g_IN)
      done
    also have "(\<Sum>\<^sup>+ y. ?g (x, y) * indicator \<^bold>E (x, y)) = d_OUT ?g x" unfolding d_OUT_def using that
      by(auto simp add: A_in split: split_indicator intro!: nn_integral_cong \<Psi>.flowD_outside[OF g])
    also have "\<dots>  = d_OUT g \<langle>x\<rangle> - g (SINK, \<langle>x\<rangle>)" using that by(rule OUT_g_A)
    also have "(\<Sum>\<^sup>+ y. ?g (y, x) * indicator \<^bold>E (x, y)) = d_IN ?g x" using that unfolding d_IN_def
      by(auto simp add: A_in split: split_indicator intro!: nn_integral_cong \<Psi>.flowD_outside[OF g])
    also have "\<dots> = d_OUT g \<langle>x\<rangle> - g (\<langle>x\<rangle>, SINK)" using that by(rule IN_g_A)
    also have "d_OUT (h 0) x + (d_OUT g \<langle>x\<rangle> - g (SINK, \<langle>x\<rangle>)) - \<dots> = d_OUT (h 0) x + g (\<langle>x\<rangle>, SINK) - g (SINK, \<langle>x\<rangle>)"
      apply(simp add: g_le_OUT add_diff_eq_ennreal d_OUT_ge_point)
      apply(subst diff_diff_commute_ennreal)
      apply(simp add: add_increasing d_OUT_ge_point g_le_OUT diff_diff_ennreal')
      apply(subst add.assoc)
      apply(subst (2) add.commute)
      apply(subst add.assoc[symmetric])
      apply(subst ennreal_add_diff_cancel_right)
      apply(simp_all add: \<Psi>.flowD_finite_OUT[OF g])
      done
    finally show ?thesis .
  qed

  have finite_g_OUT: "d_OUT ?g x \<noteq> \<top>" for x using \<alpha>_finite
  proof(rule neq_top_trans)
    have "d_OUT ?g x = (\<Sum>\<^sup>+ y\<in>range Inner. g (y, \<langle>x\<rangle>))"
      by(auto simp add: d_OUT_def nn_integral_count_space_reindex)
    also have "\<dots> \<le> d_IN g \<langle>x\<rangle>" unfolding d_IN_def
      by(auto simp add: nn_integral_count_space_indicator intro!: nn_integral_mono split: split_indicator)
    also have "\<dots> \<le> \<alpha>" using IN_g value_g by simp
    finally show "d_OUT ?g x \<le> \<alpha>" .
  qed

  have IN_h'_B: "d_IN h' x = d_IN (h 0) x + g (SOURCE, \<langle>x\<rangle>)" if "x \<in> B \<Gamma>" for x
  proof -
    have g_le: "g (SOURCE, \<langle>x\<rangle>) \<le> d_IN g \<langle>x\<rangle>"
      by (rule d_IN_ge_point)

    have "d_IN h' x = d_IN (h 0) x + (\<Sum>\<^sup>+ y. g (\<langle>x\<rangle>, \<langle>y\<rangle>) * indicator \<^bold>E (y, x)) - (\<Sum>\<^sup>+ y. g (\<langle>y\<rangle>, \<langle>x\<rangle>) * indicator \<^bold>E (y, x))"
      unfolding h'_def
      by(subst IN_plus_flow[of \<Gamma> "h 0" ?g, OF currentD_outside'[OF h]])
        (auto simp add: g_le_h0 finite_g_OUT)
    also have "(\<Sum>\<^sup>+ y. g (\<langle>x\<rangle>, \<langle>y\<rangle>) * indicator \<^bold>E (y, x)) = d_IN ?g x" unfolding d_IN_def using that
      by(intro nn_integral_cong)(auto split: split_indicator intro!: \<Psi>.flowD_outside[OF g] simp add: B_out)
    also have "\<dots> = d_OUT g \<langle>x\<rangle>" using that by(rule IN_g_B)
    also have "(\<Sum>\<^sup>+ y. g (\<langle>y\<rangle>, \<langle>x\<rangle>) * indicator \<^bold>E (y, x)) = d_OUT ?g x" unfolding d_OUT_def using that
      by(intro nn_integral_cong)(auto split: split_indicator intro!: \<Psi>.flowD_outside[OF g] simp add: B_out)
    also have "\<dots> = d_IN g \<langle>x\<rangle> - g (SOURCE, \<langle>x\<rangle>)" using that by(rule OUT_g_B)
    also have "d_IN (h 0) x + d_OUT g \<langle>x\<rangle> - \<dots> = d_IN (h 0) x + g (SOURCE, \<langle>x\<rangle>)"
      using \<Psi>.flowD_finite_IN[OF g] g_le
      by(cases "d_IN (h 0) x"; cases "d_IN g \<langle>x\<rangle>"; cases "d_IN g \<langle>x\<rangle>"; cases "g (SOURCE, \<langle>x\<rangle>)")
        (auto simp: flowD_KIR[OF g] top_add ennreal_minus_if ennreal_plus_if simp del: ennreal_plus)
    finally show ?thesis .
  qed

  have h': "current \<Gamma> h'"
  proof
    fix x
    consider (A) "x \<in> A \<Gamma>" | (B) "x \<in> B \<Gamma>" | (outside) "x \<notin> \<^bold>V" using bipartite_V by auto
    note cases = this

    show "d_OUT h' x \<le> weight \<Gamma> x"
    proof(cases rule: cases)
      case A
      then have "d_OUT h' x = d_OUT (h 0) x + g (\<langle>x\<rangle>, SINK) - g (SINK, \<langle>x\<rangle>)" by(simp add: OUT_h'_A)
      also have "\<dots> \<le> d_OUT (h 0) x + g (\<langle>x\<rangle>, SINK)" by(rule diff_le_self_ennreal)
      also have "g (\<langle>x\<rangle>, SINK) \<le> weight \<Gamma> x - d_OUT (h 0) x"
        using flowD_capacity[OF g, of "(\<langle>x\<rangle>, SINK)"] A by simp
      also have "d_OUT (h 0) x + \<dots> = weight \<Gamma> x"
        by(simp add: add_diff_eq_ennreal add_diff_inverse_ennreal  currentD_finite_OUT[OF h] currentD_weight_OUT[OF h])
      finally show ?thesis by(simp add: add_left_mono)
    qed(simp_all add: OUT_h'_outside )

    show "d_IN h' x \<le> weight \<Gamma> x"
    proof(cases rule: cases)
      case B
      hence "d_IN h' x = d_IN (h 0) x + g (SOURCE, \<langle>x\<rangle>)" by(rule IN_h'_B)
      also have "\<dots> \<le> weight \<Gamma> x"
        by(simp add: g_SOURCE \<alpha> currentD_weight_IN[OF h] add_diff_eq_ennreal add_diff_inverse_ennreal currentD_finite_IN[OF h])
      finally show ?thesis .
    qed(simp_all add:  IN_h'_outside)
  next
    show "h' e = 0" if "e \<notin> \<^bold>E" for e using that by(simp split: prod.split_asm add: h'_simps)
  qed
  moreover
  have SAT_h': "B \<Gamma> \<inter> \<^bold>V \<subseteq> SAT \<Gamma> h'"
  proof
    show "x \<in> SAT \<Gamma> h'" if "x \<in> B \<Gamma> \<inter> \<^bold>V" for x using that
    proof(cases "x = b")
      case True
      have "d_IN h' x = weight \<Gamma> x" using that True
        by(simp add: IN_h'_B g_SOURCE \<alpha> currentD_weight_IN[OF h] add_diff_eq_ennreal add_diff_inverse_ennreal currentD_finite_IN[OF h])
      thus ?thesis by(simp add: SAT.simps)
    next
      case False
      have "d_IN h' x = d_IN (h 0) x" using that False by(simp add: IN_h'_B g_SOURCE)
      also have "\<dots> = weight \<Gamma> x"
        using SAT[of 0, THEN subsetD, of x] False that currentD_SAT[OF h, of x 0] disjoint by auto
      finally show ?thesis by(simp add: SAT.simps)
    qed
  qed
  moreover
  have "wave \<Gamma> h'"
  proof
    have "separating \<Gamma> (B \<Gamma> \<inter> \<^bold>V)"
    proof
      fix x y p
      assume x: "x \<in> A \<Gamma>" and y: "y \<in> B \<Gamma>" and p: "path \<Gamma> x p y"
      hence Nil: "p \<noteq> []" using disjoint by(auto simp add: rtrancl_path_simps)
      from rtrancl_path_last[OF p Nil] last_in_set[OF Nil] y rtrancl_path_Range[OF p, of y]
      show "(\<exists>z\<in>set p. z \<in> B \<Gamma> \<inter> \<^bold>V) \<or> x \<in> B \<Gamma> \<inter> \<^bold>V" by(auto intro: vertexI2)
    qed
    moreover have TER: "B \<Gamma> \<inter> \<^bold>V \<subseteq> TER h'" using SAT_h' by(auto simp add: SINK)
    ultimately show "separating \<Gamma> (TER h')" by(rule separating_weakening)
  qed(rule h')
  ultimately show ?thesis by blast
qed

end

lemma countable_bipartite_web_reduce_weight:
  assumes "weight \<Gamma> x \<ge> w"
  shows "countable_bipartite_web (reduce_weight \<Gamma> x w)"
using bipartite_V A_vertex bipartite_E disjoint assms
by unfold_locales (auto 4 3 simp add: weight_outside )

lemma unhinder: \<comment> \<open>Lemma 6.9\<close>
  assumes loose: "loose \<Gamma>"
  and b: "b \<in> B \<Gamma>"
  and wb: "weight \<Gamma> b > 0"
  and \<delta>: "\<delta> > 0"
  shows "\<exists>\<epsilon>>0. \<epsilon> < \<delta> \<and> \<not> hindered (reduce_weight \<Gamma> b \<epsilon>)"
proof(rule ccontr)
  assume "\<not> ?thesis"
  hence hindered: "hindered (reduce_weight \<Gamma> b \<epsilon>)" if "\<epsilon> > 0" "\<epsilon> < \<delta>" for \<epsilon> using that by simp

  from b disjoint have bnA: "b \<notin> A \<Gamma>" by blast

  define wb where "wb = enn2real (weight \<Gamma> b)"
  have wb_conv: "weight \<Gamma> b = ennreal wb" by(simp add: wb_def less_top[symmetric])
  have wb_pos: "wb > 0" using wb by(simp add: wb_conv)

  define \<epsilon> where "\<epsilon> n = min \<delta> wb / (n + 2)" for n :: nat
  have \<epsilon>_pos: "\<epsilon> n > 0" for n using wb_pos \<delta> by(simp add: \<epsilon>_def)
  have \<epsilon>_nonneg: "0 \<le> \<epsilon> n" for n using \<epsilon>_pos[of n] by simp
  have *: "\<epsilon> n \<le> min wb \<delta> / 2" for n using wb_pos \<delta>
    by(auto simp add: \<epsilon>_def field_simps min_def)
  have \<epsilon>_le: "\<epsilon> n \<le> wb" and \<epsilon>_less: "\<epsilon> n < wb" and \<epsilon>_less_\<delta>: "\<epsilon> n < \<delta>" and \<epsilon>_le': "\<epsilon> n \<le> wb / 2" for n
    using *[of n] \<epsilon>_pos[of n] by(auto)

  define \<Gamma>' where "\<Gamma>' n = reduce_weight \<Gamma> b (\<epsilon> n)" for n :: nat
  have \<Gamma>'_sel [simp]:
    "edge (\<Gamma>' n) = edge \<Gamma>"
    "A (\<Gamma>' n) = A \<Gamma>"
    "B (\<Gamma>' n) = B \<Gamma>"
    "weight (\<Gamma>' n) x = weight \<Gamma> x - (if x = b then \<epsilon> n else 0)"
    "essential (\<Gamma>' n) = essential \<Gamma>"
    "roofed_gen (\<Gamma>' n) = roofed_gen \<Gamma>"
    for n x by(simp_all add: \<Gamma>'_def)

  have vertex_\<Gamma>' [simp]: "vertex (\<Gamma>' n) = vertex \<Gamma>" for n
    by(simp add: vertex_def fun_eq_iff)

  from wb have "b \<in> \<^bold>V" using weight_outside[of b] by(auto intro: ccontr)
  interpret \<Gamma>': countable_bipartite_web "\<Gamma>' n" for n unfolding \<Gamma>'_def
    using wb_pos by(intro countable_bipartite_web_reduce_weight)(simp_all add: wb_conv \<epsilon>_le \<epsilon>_nonneg)

  obtain g where g: "\<And>n. current (\<Gamma>' n) (g n)"
    and w: "\<And>n. wave (\<Gamma>' n) (g n)"
    and hind: "\<And>n. hindrance (\<Gamma>' n) (g n)" using hindered[OF \<epsilon>_pos, unfolded wb_conv ennreal_less_iff, OF \<epsilon>_less_\<delta>]
    unfolding hindered.simps \<Gamma>'_def by atomize_elim metis
  from g have g\<Gamma>: "current \<Gamma> (g n)" for n
    by(rule current_weight_mono)(auto simp add: \<epsilon>_nonneg diff_le_self_ennreal)
  note [simp] = currentD_finite[OF g\<Gamma>]

  have b_TER: "b \<in> TER\<^bsub>\<Gamma>' n\<^esub> (g n)" for n
  proof(rule ccontr)
    assume b': "b \<notin> TER\<^bsub>\<Gamma>' n\<^esub> (g n)"
    then have TER: "TER\<^bsub>\<Gamma>' n\<^esub> (g n) = TER (g n)" using b \<epsilon>_nonneg[of n]
      by(auto simp add: SAT.simps split: if_split_asm intro: ennreal_diff_le_mono_left)
    from w[of n] TER have "wave \<Gamma> (g n)" by(simp add: wave.simps separating_gen.simps)
    moreover have "hindrance \<Gamma> (g n)" using hind[of n] TER bnA b'
      by(auto simp add: hindrance.simps split: if_split_asm)
    ultimately show False using loose_unhindered[OF loose] g\<Gamma>[of n] by(auto intro: hindered.intros)
  qed

  have IN_g_b: "d_IN (g n) b = weight \<Gamma> b - \<epsilon> n" for n using b_TER[of n] bnA
    by(auto simp add: currentD_SAT[OF g])

  define factor where "factor n = (wb - \<epsilon> 0) / (wb - \<epsilon> n)" for n
  have factor_le_1: "factor n \<le> 1" for n using wb_pos \<delta> \<epsilon>_less[of n]
    by(auto simp add: factor_def field_simps \<epsilon>_def min_def)
  have factor_pos: "0 < factor n" for n using wb_pos \<delta> * \<epsilon>_less by(simp add: factor_def field_simps)
  have factor: "(wb - \<epsilon> n) * factor n = wb - \<epsilon> 0" for n using \<epsilon>_less[of n]
    by(simp add: factor_def field_simps)

  define g' where "g' = (\<lambda>n (x, y). if y = b then g n (x, y) * factor n else g n (x, y))"
  have g'_simps: "g' n (x, y) = (if y = b then g n (x, y) * factor n else g n (x, y))" for n x y by(simp add: g'_def)
  have g'_le_g: "g' n e \<le> g n e" for n e using factor_le_1[of n]
    by(cases e "g n e" rule: prod.exhaust[case_product ennreal_cases])
      (auto simp add: g'_simps field_simps mult_left_le)

  have "4 + (n * 6 + n * (n * 2)) \<noteq> (0 :: real)" for n :: nat
    by(metis (mono_tags, hide_lams) add_is_0 of_nat_eq_0_iff of_nat_numeral zero_neq_numeral)
  then have IN_g': "d_IN (g' n) x = (if x = b then weight \<Gamma> b - \<epsilon> 0 else d_IN (g n) x)" for x n
    using b_TER[of n] bnA factor_pos[of n] factor[of n] wb_pos \<delta>
    by(auto simp add: d_IN_def g'_simps nn_integral_divide nn_integral_cmult currentD_SAT[OF g] wb_conv \<epsilon>_def field_simps
                      ennreal_minus ennreal_mult'[symmetric] intro!: arg_cong[where f=ennreal])
  have OUT_g': "d_OUT (g' n) x = d_OUT (g n) x - g n (x, b) * (1 - factor n)" for n x
  proof -
    have "d_OUT (g' n) x = (\<Sum>\<^sup>+ y. g n (x, y)) - (\<Sum>\<^sup>+ y. (g n (x, y) * (1 - factor n)) * indicator {b} y)"
      using factor_le_1[of n] factor_pos[of n]
      apply(cases "g n (x, b)")
      apply(subst nn_integral_diff[symmetric])
      apply(auto simp add: g'_simps nn_integral_divide d_OUT_def AE_count_space mult_left_le ennreal_mult_eq_top_iff
                           ennreal_mult'[symmetric] ennreal_minus_if
                 intro!: nn_integral_cong split: split_indicator)
      apply(simp_all add: field_simps)
      done
    also have "\<dots> = d_OUT (g n) x - g n (x, b) * (1 - factor n)" using factor_le_1[of n]
      by(subst nn_integral_indicator_singleton)(simp_all add: d_OUT_def field_simps)
    finally show ?thesis .
  qed

  have g': "current (\<Gamma>' 0) (g' n)" for n
  proof
    show "d_OUT (g' n) x \<le> weight (\<Gamma>' 0) x" for x
      using b_TER[of n] currentD_weight_OUT[OF g, of n x] \<epsilon>_le[of 0] factor_le_1[of n]
      by(auto simp add: OUT_g' SINK.simps ennreal_diff_le_mono_left)
    show "d_IN (g' n) x \<le> weight (\<Gamma>' 0) x" for x
      using d_IN_mono[of "g' n" x, OF g'_le_g] currentD_weight_IN[OF g, of n x] b_TER[of n] b
      by(auto simp add: IN_g' SAT.simps wb_conv \<epsilon>_def)
    show "g' n e = 0" if "e \<notin> \<^bold>E\<^bsub>\<Gamma>' 0\<^esub>" for e using that by(cases e)(clarsimp simp add: g'_simps currentD_outside[OF g])
  qed

  have SINK_g': "SINK (g n) = SINK (g' n)" for n using factor_pos[of n]
    by(auto simp add: SINK.simps currentD_OUT_eq_0[OF g] currentD_OUT_eq_0[OF g'] g'_simps split: if_split_asm)
  have SAT_g': "SAT (\<Gamma>' n) (g n) = SAT (\<Gamma>' 0) (g' n)" for n using b_TER[of n] \<epsilon>_le'[of 0]
    by(auto simp add: SAT.simps wb_conv IN_g' IN_g_b)
  have TER_g': "TER\<^bsub>\<Gamma>' n\<^esub> (g n) = TER\<^bsub>\<Gamma>' 0\<^esub> (g' n)" for n
    using b_TER[of n] by(auto simp add: SAT.simps SINK_g' OUT_g' IN_g' wb_conv \<epsilon>_def)

  have w': "wave (\<Gamma>' 0) (g' n)" for n
  proof
    have "separating (\<Gamma>' 0) (TER\<^bsub>\<Gamma>' n\<^esub> (g n))" using waveD_separating[OF w, of n]
      by(simp add: separating_gen.simps)
    then show "separating (\<Gamma>' 0) (TER\<^bsub>\<Gamma>' 0\<^esub> (g' n))" unfolding TER_g' .
  qed(rule g')

  define f where "f = rec_nat (g 0) (\<lambda>n rec. rec \<frown>\<^bsub>\<Gamma>' 0\<^esub> g' (n + 1))"
  have f_simps [simp]:
    "f 0 = g 0"
    "f (Suc n) = f n \<frown>\<^bsub>\<Gamma>' 0\<^esub> g' (n + 1)"
    for n by(simp_all add: f_def)

  have f: "current (\<Gamma>' 0) (f n)" and fw: "wave (\<Gamma>' 0) (f n)" for n
  proof(induction n)
    case (Suc n)
    { case 1 show ?case unfolding f_simps using Suc.IH g' by(rule current_plus_web) }
    { case 2 show ?case unfolding f_simps using Suc.IH g' w' by(rule wave_plus') }
  qed(simp_all add: g w)

  have f_inc: "n \<le> m \<Longrightarrow> f n \<le> f m" for n m
  proof(induction m rule: dec_induct)
    case (step k)
    note step.IH
    also have "f k \<le> (f k \<frown>\<^bsub>\<Gamma>' 0\<^esub> g' (k + 1))"
      by(rule le_funI plus_web_greater)+
    also have "\<dots> = f (Suc k)" by simp
    finally show ?case .
  qed simp
  have chain_f: "Complete_Partial_Order.chain (\<le>) (range f)"
    by(rule chain_imageI[where le_a="(\<le>)"])(simp_all add: f_inc)
  have "countable (support_flow (f n))" for n using current_support_flow[OF f, of n]
    by(rule countable_subset) simp
  hence supp_f: "countable (support_flow (SUP n. f n))" by(subst support_flow_Sup)simp

  have RF_f: "RF (TER\<^bsub>\<Gamma>' 0\<^esub> (f n)) = RF (\<Union>i\<le>n. TER\<^bsub>\<Gamma>' 0\<^esub> (g' i))" for n
  proof(induction n)
    case 0 show ?case by(simp add: TER_g')
  next
    case (Suc n)
    have "RF (TER\<^bsub>\<Gamma>' 0\<^esub> (f (Suc n))) = RF\<^bsub>\<Gamma>' 0\<^esub> (TER\<^bsub>\<Gamma>' 0\<^esub> (f n \<frown>\<^bsub>\<Gamma>' 0\<^esub> g' (n + 1)))" by simp
    also have "\<dots> = RF\<^bsub>\<Gamma>' 0\<^esub> (TER\<^bsub>\<Gamma>' 0\<^esub> (f n) \<union> TER\<^bsub>\<Gamma>' 0\<^esub> (g' (n + 1)))" using f fw g' w'
      by(rule RF_TER_plus_web)
    also have "\<dots> = RF\<^bsub>\<Gamma>' 0\<^esub> (RF\<^bsub>\<Gamma>' 0\<^esub> (TER\<^bsub>\<Gamma>' 0\<^esub> (f n)) \<union> TER\<^bsub>\<Gamma>' 0\<^esub> (g' (n + 1)))"
      by(simp add: roofed_idem_Un1)
    also have "RF\<^bsub>\<Gamma>' 0\<^esub> (TER\<^bsub>\<Gamma>' 0\<^esub> (f n)) = RF\<^bsub>\<Gamma>' 0\<^esub> (\<Union>i\<le>n. TER\<^bsub>\<Gamma>' 0\<^esub> (g' i))" by(simp add: Suc.IH)
    also have "RF\<^bsub>\<Gamma>' 0\<^esub> (\<dots> \<union> TER\<^bsub>\<Gamma>' 0\<^esub> (g' (n + 1))) = RF\<^bsub>\<Gamma>' 0\<^esub> ((\<Union>i\<le>n. TER\<^bsub>\<Gamma>' 0\<^esub> (g' i)) \<union> TER\<^bsub>\<Gamma>' 0\<^esub> (g' (n + 1)))"
      by(simp add: roofed_idem_Un1)
    also have "(\<Union>i\<le>n. TER\<^bsub>\<Gamma>' 0\<^esub> (g' i)) \<union> TER\<^bsub>\<Gamma>' 0\<^esub> (g' (n + 1)) = (\<Union>i\<le>Suc n. TER\<^bsub>\<Gamma>' 0\<^esub> (g' i))"
      unfolding atMost_Suc UN_insert by(simp add: Un_commute)
    finally show ?case by simp
  qed

  define g\<omega> where "g\<omega> = (SUP n. f n)"
  have g\<omega>: "current (\<Gamma>' 0) g\<omega>" unfolding g\<omega>_def using chain_f
    by(rule current_Sup)(auto simp add: f supp_f)
  have w\<omega>: "wave (\<Gamma>' 0) g\<omega>" unfolding g\<omega>_def using chain_f
    by(rule wave_lub)(auto simp add: fw  supp_f)
  from g\<omega> have g\<omega>': "current (\<Gamma>' n) g\<omega>" for n using wb_pos \<delta>
    by(elim current_weight_mono)(auto simp add: \<epsilon>_le wb_conv \<epsilon>_def field_simps ennreal_minus_if min_le_iff_disj)

  have SINK_g\<omega>: "SINK g\<omega> = (\<Inter>n. SINK (f n))" unfolding g\<omega>_def
    by(subst SINK_Sup[OF chain_f])(simp_all add: supp_f)
  have SAT_g\<omega>: "SAT (\<Gamma>' 0) (f n) \<subseteq> SAT (\<Gamma>' 0) g\<omega>" for n
    unfolding g\<omega>_def by(rule SAT_Sup_upper) simp

  have g_b_out: "g n (b, x) = 0" for n x using b_TER[of n] by(simp add: SINK.simps currentD_OUT_eq_0[OF g])
  have g'_b_out: "g' n (b, x) = 0" for n x by(simp add: g'_simps g_b_out)
  have "f n (b, x) = 0" for n x by(induction n)(simp_all add: g_b_out g'_b_out)
  hence b_SINK_f: "b \<in> SINK (f n)" for n by(simp add: SINK.simps d_OUT_def)
  hence b_SINK_g\<omega>: "b \<in> SINK g\<omega>" by(simp add: SINK_g\<omega>)

  have RF_circ: "RF\<^sup>\<circ>\<^bsub>\<Gamma>' n\<^esub> (TER\<^bsub>\<Gamma>' 0\<^esub> (g' n)) = RF\<^sup>\<circ>\<^bsub>\<Gamma>' 0\<^esub> (TER\<^bsub>\<Gamma>' 0\<^esub> (g' n))" for n by(simp add: roofed_circ_def)
  have edge_restrict_\<Gamma>': "edge (quotient_web (\<Gamma>' 0) (g' n)) = edge (quotient_web (\<Gamma>' n) (g n))" for n
    by(simp add: fun_eq_iff TER_g' RF_circ)
  have restrict_curr_g': "f \<upharpoonleft> \<Gamma>' 0 / g' n = f \<upharpoonleft> \<Gamma>' n / g n" for n f
    by(simp add: restrict_current_def RF_circ TER_g')

  have RF_restrict: "roofed_gen (quotient_web (\<Gamma>' n) (g n)) = roofed_gen (quotient_web (\<Gamma>' 0) (g' n))" for n
    by(simp add: roofed_def fun_eq_iff edge_restrict_\<Gamma>')

  have g\<omega>r': "current (quotient_web (\<Gamma>' 0) (g' n)) (g\<omega> \<upharpoonleft> \<Gamma>' 0 / g' n)" for n using w' g\<omega>
    by(rule current_restrict_current)
  have g\<omega>r: "current (quotient_web (\<Gamma>' n) (g n)) (g\<omega> \<upharpoonleft> \<Gamma>' n / g n)" for n using w g\<omega>'
    by(rule current_restrict_current)
  have w\<omega>r: "wave (quotient_web (\<Gamma>' n) (g n)) (g\<omega> \<upharpoonleft> \<Gamma>' n / g n)" (is "wave ?\<Gamma>' ?g\<omega>") for n
  proof
    have *: "wave (quotient_web (\<Gamma>' 0) (g' n)) (g\<omega> \<upharpoonleft> \<Gamma>' 0 / g' n)"
      using g' w' g\<omega> w\<omega> by(rule wave_restrict_current)
    have "d_IN (g\<omega> \<upharpoonleft> \<Gamma>' n / g n) b = 0"
      by(rule d_IN_restrict_current_outside roofed_greaterI b_TER)+
    hence SAT_subset: "SAT (quotient_web (\<Gamma>' 0) (g' n)) (g\<omega> \<upharpoonleft> \<Gamma>' n / g n) \<subseteq> SAT ?\<Gamma>' (g\<omega> \<upharpoonleft> \<Gamma>' n / g n)"
      using b_TER[of n] wb_pos
      by(auto simp add: SAT.simps TER_g' RF_circ wb_conv \<epsilon>_def field_simps
                        ennreal_minus_if split: if_split_asm)
    hence TER_subset: "TER\<^bsub>quotient_web (\<Gamma>' 0) (g' n)\<^esub> (g\<omega> \<upharpoonleft> \<Gamma>' n / g n) \<subseteq> TER\<^bsub>?\<Gamma>'\<^esub> (g\<omega> \<upharpoonleft> \<Gamma>' n / g n)"
      using SINK_g' by(auto simp add: restrict_curr_g')

    show "separating ?\<Gamma>' (TER\<^bsub>?\<Gamma>'\<^esub> ?g\<omega>)" (is "separating _ ?TER")
    proof
      fix x y p
      assume xy: "x \<in> A ?\<Gamma>'" "y \<in> B ?\<Gamma>'" and p: "path ?\<Gamma>' x p y"
      from p have p': "path (quotient_web (\<Gamma>' 0) (g' n)) x p y" by(simp add: edge_restrict_\<Gamma>')
      with waveD_separating[OF *, THEN separatingD, simplified, OF p'] TER_g'[of n] SINK_g' SAT_g' restrict_curr_g' SAT_subset xy
      show "(\<exists>z\<in>set p. z \<in> ?TER) \<or> x \<in> ?TER" by auto
    qed

    show "d_OUT (g\<omega> \<upharpoonleft> \<Gamma>' n / g n) x = 0" if "x \<notin> RF\<^bsub>?\<Gamma>'\<^esub> ?TER" for x
      unfolding restrict_curr_g'[symmetric] using TER_subset that
      by(intro waveD_OUT[OF *])(auto simp add: TER_g' restrict_curr_g' RF_restrict intro: in_roofed_mono)
  qed

  have RF_g\<omega>: "RF (TER\<^bsub>\<Gamma>' 0\<^esub> g\<omega>) = RF (\<Union>n. TER\<^bsub>\<Gamma>' 0\<^esub> (g' n))"
  proof -
    have "RF\<^bsub>\<Gamma>' 0\<^esub> (TER\<^bsub>\<Gamma>' 0\<^esub> g\<omega>) = RF (\<Union>i. TER\<^bsub>\<Gamma>' 0\<^esub> (f i))"
      unfolding g\<omega>_def by(subst RF_TER_Sup[OF _ _ chain_f])(auto simp add: f fw supp_f)
    also have "\<dots> = RF (\<Union>i. RF (TER\<^bsub>\<Gamma>' 0\<^esub> (f i)))" by(simp add: roofed_UN)
    also have "\<dots> = RF (\<Union>i. \<Union>j\<le>i. TER\<^bsub>\<Gamma>' 0\<^esub> (g' j))" unfolding RF_f roofed_UN by simp
    also have "(\<Union>i. \<Union>j\<le>i. TER\<^bsub>\<Gamma>' 0\<^esub> (g' j)) = (\<Union>i. TER\<^bsub>\<Gamma>' 0\<^esub> (g' i))" by auto
    finally show ?thesis by simp
  qed

  have SAT_plus_\<omega>: "SAT (\<Gamma>' n) (g n \<frown>\<^bsub>\<Gamma>' n\<^esub> g\<omega>) = SAT (\<Gamma>' 0) (g' n \<frown>\<^bsub>\<Gamma>' 0\<^esub> g\<omega>)" for n
    apply(intro set_eqI)
    apply(simp add: SAT.simps IN_plus_current[OF g w g\<omega>r] IN_plus_current[OF g' w' g\<omega>r'] TER_g')
    apply(cases "d_IN (g\<omega> \<upharpoonleft> \<Gamma>' n / g n) b")
    apply(auto simp add: SAT.simps wb_conv d_IN_plus_web IN_g')
    apply(simp_all add: wb_conv IN_g_b restrict_curr_g' \<epsilon>_def field_simps)
    apply(metis TER_g' b_TER roofed_greaterI)+
    done
  have SINK_plus_\<omega>: "SINK (g n \<frown>\<^bsub>\<Gamma>' n\<^esub> g\<omega>) = SINK (g' n \<frown>\<^bsub>\<Gamma>' 0\<^esub> g\<omega>)" for n
    apply(rule set_eqI; simp add: SINK.simps OUT_plus_current[OF g w g\<omega>r] OUT_plus_current[OF g' w'] current_restrict_current[OF w' g\<omega>])
    using factor_pos[of n]
    by(auto simp add: RF_circ TER_g' restrict_curr_g' currentD_OUT_eq_0[OF g] currentD_OUT_eq_0[OF g'] g'_simps split: if_split_asm)
  have TER_plus_\<omega>: "TER\<^bsub>\<Gamma>' n\<^esub> (g n \<frown>\<^bsub>\<Gamma>' n\<^esub> g\<omega>) = TER\<^bsub>\<Gamma>' 0\<^esub> (g' n \<frown>\<^bsub>\<Gamma>' 0\<^esub> g\<omega>)" for n
    by(rule set_eqI iffI)+(simp_all add: SAT_plus_\<omega> SINK_plus_\<omega>)

  define h where "h n = g n \<frown>\<^bsub>\<Gamma>' n\<^esub> g\<omega>" for n
  have h: "current (\<Gamma>' n) (h n)" for n unfolding h_def using g w
    by(rule current_plus_current)(rule current_restrict_current[OF w g\<omega>'])
  have hw: "wave (\<Gamma>' n) (h n)" for n unfolding h_def using g w g\<omega>' w\<omega>r by(rule wave_plus)

  define T where "T = TER\<^bsub>\<Gamma>' 0\<^esub> g\<omega>"
  have RF_h: "RF (TER\<^bsub>\<Gamma>' n\<^esub> (h n)) = RF T" for n
  proof -
    have "RF\<^bsub>\<Gamma>' 0\<^esub> (TER\<^bsub>\<Gamma>' n\<^esub> (h n)) = RF\<^bsub>\<Gamma>' 0\<^esub> (RF\<^bsub>\<Gamma>' 0\<^esub> (TER\<^bsub>\<Gamma>' 0\<^esub> g\<omega>) \<union> TER\<^bsub>\<Gamma>' 0\<^esub> (g' n))"
      unfolding h_def TER_plus_\<omega> RF_TER_plus_web[OF g' w' g\<omega> w\<omega>] roofed_idem_Un1 by(simp add: Un_commute)
    also have "\<dots> = RF ((\<Union>n. TER\<^bsub>\<Gamma>' 0\<^esub> (g' n)) \<union> TER\<^bsub>\<Gamma>' 0\<^esub> (g' n))"
      by(simp add: RF_g\<omega> roofed_idem_Un1)
    also have "\<dots> = RF\<^bsub>\<Gamma>' 0\<^esub> T" unfolding T_def
      by(auto simp add: RF_g\<omega> intro!: arg_cong2[where f=roofed] del: equalityI) auto
    finally show ?thesis by simp
  qed
  have OUT_h_nT: "d_OUT (h n) x = 0" if "x \<notin> RF T" for n x
    by(rule waveD_OUT[OF hw])(simp add: RF_h that)
  have IN_h_nT: "d_IN (h n) x = 0" if "x \<notin> RF T" for n x
    by(rule wave_not_RF_IN_zero[OF h hw])(simp add: RF_h that)
  have OUT_h_b: "d_OUT (h n) b = 0" for n using b_TER[of n] b_SINK_g\<omega>[THEN in_SINK_restrict_current]
    by(auto simp add: h_def OUT_plus_current[OF g w g\<omega>r] SINK.simps)
  have OUT_h_\<E>: "d_OUT (h n) x = 0" if "x \<in> \<E> T" for x n using that
    apply(subst (asm) \<E>_RF[symmetric])
    apply(subst (asm) (1 2) RF_h[symmetric, of n])
    apply(subst (asm) \<E>_RF)
    apply(simp add: SINK.simps)
    done
  have IN_h_\<E>: "d_IN (h n) x = weight (\<Gamma>' n) x" if "x \<in> \<E> T" "x \<notin> A \<Gamma>" for x n using that
    apply(subst (asm) \<E>_RF[symmetric])
    apply(subst (asm) (1 2) RF_h[symmetric, of n])
    apply(subst (asm) \<E>_RF)
    apply(simp add: currentD_SAT[OF h])
    done

  have b_SAT: "b \<in> SAT (\<Gamma>' 0) (h 0)" using b_TER[of 0]
    by(auto simp add: h_def SAT.simps d_IN_plus_web intro: order_trans)
  have b_T: "b \<in> T" using b_SINK_g\<omega> b_TER by(simp add: T_def)(metis SAT_g\<omega> subsetD f_simps(1))

  have essential: "b \<in> \<E> T"
  proof(rule ccontr)
    assume "b \<notin> \<E> T"
    hence b: "b \<notin> \<E> (TER\<^bsub>\<Gamma>' 0\<^esub> (h 0))"
    proof(rule contrapos_nn)
      assume "b \<in> \<E> (TER\<^bsub>\<Gamma>' 0\<^esub> (h 0))"
      then obtain p y where p: "path \<Gamma> b p y" and y: "y \<in> B \<Gamma>" and distinct: "distinct (b # p)"
        and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER\<^bsub>\<Gamma>' 0\<^esub> (h 0))" by(rule \<E>_E_RF) auto
      from bypass have bypass': "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> T" unfolding RF_h by(auto intro: roofed_greaterI)
      have "essential \<Gamma> (B \<Gamma>) T b" using p y by(rule essentialI)(auto dest: bypass')
      then show "b \<in> \<E> T" using b_T by simp
    qed

    have h0: "current \<Gamma> (h 0)" using h[of 0] by(rule current_weight_mono)(simp_all add: wb_conv \<epsilon>_nonneg)
    moreover have "wave \<Gamma> (h 0)"
    proof
      have "separating (\<Gamma>' 0) (\<E>\<^bsub>\<Gamma>' 0\<^esub> (TER\<^bsub>\<Gamma>' 0\<^esub> (h 0)))" by(rule separating_essential)(rule waveD_separating[OF hw])
      then have "separating \<Gamma> (\<E> (TER\<^bsub>\<Gamma>' 0\<^esub> (h 0)))" by(simp add: separating_gen.simps)
      moreover have subset: "\<E> (TER\<^bsub>\<Gamma>' 0\<^esub> (h 0)) \<subseteq> TER (h 0)" using \<epsilon>_nonneg[of 0] b
        by(auto simp add: SAT.simps wb_conv split: if_split_asm)
      ultimately show "separating \<Gamma> (TER (h 0))" by(rule separating_weakening)
    qed(rule h0)
    ultimately have "h 0 = zero_current" by(rule looseD_wave[OF loose])
    then have "d_IN (h 0) b = 0" by(simp)
    with b_SAT wb \<open>b \<notin> A \<Gamma>\<close> show False by(simp add: SAT.simps wb_conv \<epsilon>_def ennreal_minus_if split: if_split_asm)
  qed

  define S where "S = {x \<in> RF (T \<inter> B \<Gamma>) \<inter> A \<Gamma>. essential \<Gamma> (T \<inter> B \<Gamma>) (RF (T \<inter> B \<Gamma>) \<inter> A \<Gamma>) x}"
  define \<Gamma>_h where "\<Gamma>_h = \<lparr> edge = \<lambda>x y. edge \<Gamma> x y \<and> x \<in> S \<and> y \<in> T \<and> y \<in> B \<Gamma>, weight = \<lambda>x. weight \<Gamma> x * indicator (S \<union> T \<inter> B \<Gamma>) x, A = S, B = T \<inter> B \<Gamma>\<rparr>"
  have \<Gamma>_h_sel [simp]:
    "edge \<Gamma>_h x y \<longleftrightarrow> edge \<Gamma> x y \<and> x \<in> S \<and> y \<in> T \<and> y \<in> B \<Gamma>"
    "A \<Gamma>_h = S"
    "B \<Gamma>_h = T \<inter> B \<Gamma>"
    "weight \<Gamma>_h x = weight \<Gamma> x * indicator (S \<union> T \<inter> B \<Gamma>) x"
    for x y
    by(simp_all add: \<Gamma>_h_def)

  have vertex_\<Gamma>_hD: "x \<in> S \<union> (T \<inter> B \<Gamma>)" if "vertex \<Gamma>_h x" for x
    using that by(auto simp add: vertex_def)
  have S_vertex: "vertex \<Gamma>_h x" if "x \<in> S" for x
  proof -
    from that have a: "x \<in> A \<Gamma>" and RF: "x \<in> RF (T \<inter> B \<Gamma>)" and ess: "essential \<Gamma> (T \<inter> B \<Gamma>) (RF (T \<inter> B \<Gamma>) \<inter> A \<Gamma>) x"
      by(simp_all add: S_def)
    from ess obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>" and yT: "y \<in> T"
      and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (T \<inter> B \<Gamma>) \<inter> A \<Gamma>" by(rule essentialE_RF)(auto intro: roofed_greaterI)
    from p a y disjoint have "edge \<Gamma> x y"
      by(cases)(auto 4 3 elim: rtrancl_path.cases dest: bipartite_E)
    with that y yT show ?thesis by(auto intro!: vertexI1)
  qed
  have OUT_not_S: "d_OUT (h n) x = 0" if "x \<notin> S" for x n
  proof(rule classical)
    assume *: "d_OUT (h n) x \<noteq> 0"
    consider (A) "x \<in> A \<Gamma>" | (B) "x \<in> B \<Gamma>" | (outside) "x \<notin> A \<Gamma>" "x \<notin> B \<Gamma>" by blast
    then show ?thesis
    proof cases
      case B with currentD_OUT[OF h, of x n] show ?thesis by simp
    next
      case outside with currentD_outside_OUT[OF h, of x n] show ?thesis by(simp add: not_vertex)
    next
      case A
      from * obtain y where xy: "h n (x, y) \<noteq> 0" using currentD_OUT_eq_0[OF h, of n x] by auto
      then have edge: "edge \<Gamma> x y" using currentD_outside[OF h] by(auto)
      hence p: "path \<Gamma> x [y] y" by(simp add: rtrancl_path_simps)

      from bipartite_E[OF edge] have x: "x \<in> A \<Gamma>" and y: "y \<in> B \<Gamma>" by simp_all
      moreover have "x \<in> RF (RF (T \<inter> B \<Gamma>))"
      proof
        fix p y'
        assume p: "path \<Gamma> x p y'" and y': "y' \<in> B \<Gamma>"
        from p x y' disjoint have py: "p = [y']"
          by(cases)(auto 4 3 elim: rtrancl_path.cases dest: bipartite_E)
        have "separating (\<Gamma>' 0) (RF\<^bsub>\<Gamma>' 0\<^esub> (TER\<^bsub>\<Gamma>' 0\<^esub> (h 0)))" unfolding separating_RF
          by(rule waveD_separating[OF hw])
        from separatingD[OF this, of x p y'] py p x y'
        have "x \<in> RF T \<or> y' \<in> RF T" by(auto simp add: RF_h)
        thus "(\<exists>z\<in>set p. z \<in> RF (T \<inter> B \<Gamma>)) \<or> x \<in> RF (T \<inter> B \<Gamma>)"
        proof cases
          case right with y' py show ?thesis by(simp add: RF_in_B)
        next
          case left
          have "x \<notin> \<E> T" using OUT_h_\<E>[of x n] xy by(auto simp add: currentD_OUT_eq_0[OF h])
          with left have "x \<in> RF\<^sup>\<circ> T" by(simp add: roofed_circ_def)
          from RF_circ_edge_forward[OF this, of y'] p py have "y' \<in> RF T" by(simp add: rtrancl_path_simps)
          with y' have "y' \<in> T" by(simp add: RF_in_B)
          with y' show ?thesis using py by(auto intro: roofed_greaterI)
        qed
      qed
      moreover have "y \<in> T" using IN_h_nT[of y n] y xy by(auto simp add: RF_in_B currentD_IN_eq_0[OF h])
      with p x y disjoint have "essential \<Gamma> (T \<inter> B \<Gamma>) (RF (T \<inter> B \<Gamma>) \<inter> A \<Gamma>) x" by(auto intro!: essentialI)
      ultimately have "x \<in> S" unfolding roofed_idem by(simp add: S_def)
      with that show ?thesis by contradiction
    qed
  qed

  have B_vertex: "vertex \<Gamma>_h y" if T: "y \<in> T" and B: "y \<in> B \<Gamma>" and w: "weight \<Gamma> y > 0" for y
  proof -
    from T B disjoint \<epsilon>_less[of 0] w
    have "d_IN (h 0) y > 0" using IN_h_\<E>[of y 0] by(cases "y \<in> A \<Gamma>")(auto simp add: essential_BI wb_conv ennreal_minus_if)
    then obtain x where xy: "h 0 (x, y) \<noteq> 0" using currentD_IN_eq_0[OF h, of 0 y] by(auto)
    then have edge: "edge \<Gamma> x y" using currentD_outside[OF h] by(auto)
    from xy have "d_OUT (h 0) x \<noteq> 0" by(auto simp add: currentD_OUT_eq_0[OF h])
    hence "x \<in> S" using OUT_not_S[of x 0] by(auto)
    with edge T B show ?thesis by(simp add: vertexI2)
  qed

  have \<Gamma>_h: "countable_bipartite_web \<Gamma>_h"
  proof
    show "\<^bold>V\<^bsub>\<Gamma>_h\<^esub> \<subseteq> A \<Gamma>_h \<union> B \<Gamma>_h" by(auto simp add: vertex_def)
    show "A \<Gamma>_h \<subseteq> \<^bold>V\<^bsub>\<Gamma>_h\<^esub>" using S_vertex by auto
    show "x \<in> A \<Gamma>_h \<and> y \<in> B \<Gamma>_h" if "edge \<Gamma>_h x y" for x y using that by auto
    show "A \<Gamma>_h \<inter> B \<Gamma>_h = {}" using disjoint by(auto simp add: S_def)
    have "\<^bold>E\<^bsub>\<Gamma>_h\<^esub> \<subseteq> \<^bold>E" by auto
    thus "countable \<^bold>E\<^bsub>\<Gamma>_h\<^esub>" by(rule countable_subset) simp
    show "weight \<Gamma>_h x \<noteq> \<top>" for x by(simp split: split_indicator)
    show "weight \<Gamma>_h x = 0" if "x \<notin> \<^bold>V\<^bsub>\<Gamma>_h\<^esub>" for x
      using that S_vertex B_vertex[of x]
      by(cases "weight \<Gamma>_h x > 0")(auto split: split_indicator)
  qed
  then interpret \<Gamma>_h: countable_bipartite_web \<Gamma>_h .

  have essential_T: "essential \<Gamma> (B \<Gamma>) T = essential \<Gamma> (B \<Gamma>) (TER\<^bsub>\<Gamma>' 0\<^esub> (h 0))"
  proof(rule ext iffI)+
    fix x
    assume "essential \<Gamma> (B \<Gamma>) T x"
    then obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>" and distinct: "distinct (x # p)"
      and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF T" by(rule essentialE_RF)auto
    from bypass have bypass': "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> TER\<^bsub>\<Gamma>' 0\<^esub> (h 0)"
      unfolding RF_h[of 0, symmetric] by(blast intro: roofed_greaterI)
    show "essential \<Gamma> (B \<Gamma>) (TER\<^bsub>\<Gamma>' 0\<^esub> (h 0)) x" using p y
      by(blast intro: essentialI dest: bypass')
  next
    fix x
    assume "essential \<Gamma> (B \<Gamma>) (TER\<^bsub>\<Gamma>' 0\<^esub> (h 0)) x"
    then obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>" and distinct: "distinct (x # p)"
      and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER\<^bsub>\<Gamma>' 0\<^esub> (h 0))" by(rule essentialE_RF)auto
    from bypass have bypass': "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> T"
      unfolding RF_h[of 0] by(blast intro: roofed_greaterI)
    show "essential \<Gamma> (B \<Gamma>) T x" using p y
      by(blast intro: essentialI dest: bypass')
  qed

  have h': "current \<Gamma>_h (h n)" for n
  proof
    show "d_OUT (h n) x \<le> weight \<Gamma>_h x" for x
      using currentD_weight_OUT[OF h, of n x] \<epsilon>_nonneg[of n] \<Gamma>'.currentD_OUT'[OF h, of x n] OUT_not_S
      by(auto split: split_indicator if_split_asm elim: order_trans intro: diff_le_self_ennreal in_roofed_mono simp add: OUT_h_b  roofed_circ_def)

    show "d_IN (h n) x \<le> weight \<Gamma>_h x" for x
      using currentD_weight_IN[OF h, of n x] currentD_IN[OF h, of x n] \<epsilon>_nonneg[of n] b_T b \<Gamma>'.currentD_IN'[OF h, of x n] IN_h_nT[of x n]
      by(cases "x \<in> B \<Gamma>")(auto 4 3 split: split_indicator split: if_split_asm elim: order_trans intro: diff_le_self_ennreal simp add: S_def  roofed_circ_def RF_in_B)

    show "h n e = 0" if "e \<notin> \<^bold>E\<^bsub>\<Gamma>_h\<^esub>" for e
      using that OUT_not_S[of "fst e" n] currentD_outside'[OF h, of e n] \<Gamma>'.currentD_IN'[OF h, of "snd e" n] disjoint
      apply(cases "e \<in> \<^bold>E")
      apply(auto split: prod.split_asm simp add: currentD_OUT_eq_0[OF h] currentD_IN_eq_0[OF h])
      apply(cases "fst e \<in> S"; clarsimp simp add: S_def)
      apply(frule RF_circ_edge_forward[rotated])
      apply(erule roofed_circI, blast)
      apply(drule bipartite_E)
      apply(simp add: RF_in_B)
      done
  qed

  have SAT_h': "B \<Gamma>_h \<inter> \<^bold>V\<^bsub>\<Gamma>_h\<^esub> - {b} \<subseteq> SAT \<Gamma>_h (h n)" for n
  proof
    fix x
    assume "x \<in> B \<Gamma>_h \<inter> \<^bold>V\<^bsub>\<Gamma>_h\<^esub> - {b}"
    then have x: "x \<in> T" and B: "x \<in> B \<Gamma>" and b: "x \<noteq> b" and vertex: "x \<in> \<^bold>V\<^bsub>\<Gamma>_h\<^esub>" by auto
    from B disjoint have xnA: "x \<notin> A \<Gamma>" by blast
    from x B have "x \<in> \<E> T" by(simp add: essential_BI)
    hence "d_IN (h n) x = weight (\<Gamma>' n) x" using xnA by(rule IN_h_\<E>)
    with xnA b x B show "x \<in> SAT \<Gamma>_h (h n)" by(simp add: currentD_SAT[OF h'])
  qed
  moreover have "b \<in> B \<Gamma>_h" using b essential by simp
  moreover have "(\<lambda>n. min \<delta> wb * (1 / (real (n + 2)))) \<longlonglongrightarrow> 0"
    apply(rule LIMSEQ_ignore_initial_segment)
    apply(rule tendsto_mult_right_zero)
    apply(rule lim_1_over_real_power[where s=1, simplified])
    done
  then have "(INF n. ennreal (\<epsilon> n)) = 0" using wb_pos \<delta>
    apply(simp add: \<epsilon>_def)
    apply(rule INF_Lim)
    apply(rule decseq_SucI)
    apply(simp add: field_simps min_def)
    apply(simp add: add.commute ennreal_0[symmetric] del: ennreal_0)
    done
  then have "(SUP n. d_IN (h n) b) = weight \<Gamma>_h b" using essential b bnA wb IN_h_\<E>[of b]
    by(simp add: SUP_const_minus_ennreal)
  moreover have "d_IN (h 0) b \<le> d_IN (h n) b" for n using essential b bnA wb_pos \<delta> IN_h_\<E>[of b]
    by(simp add: wb_conv \<epsilon>_def field_simps ennreal_minus_if min_le_iff_disj)
  moreover have b_V: "b \<in> \<^bold>V\<^bsub>\<Gamma>_h\<^esub>" using b wb essential by(auto dest: B_vertex)
  ultimately have "\<exists>h'. current \<Gamma>_h h' \<and> wave \<Gamma>_h h' \<and> B \<Gamma>_h \<inter> \<^bold>V\<^bsub>\<Gamma>_h\<^esub> \<subseteq> SAT \<Gamma>_h h'"
    by(rule \<Gamma>_h.unhinder_bipartite[OF h'])
  then obtain h' where h': "current \<Gamma>_h h'" and h'w: "wave \<Gamma>_h h'"
    and B_SAT': "B \<Gamma>_h \<inter> \<^bold>V\<^bsub>\<Gamma>_h\<^esub> \<subseteq> SAT \<Gamma>_h h'" by blast

  have h'': "current \<Gamma> h'"
  proof
    show "d_OUT h' x \<le> weight \<Gamma> x" for x using currentD_weight_OUT[OF h', of x]
      by(auto split: split_indicator_asm elim: order_trans intro: )
    show "d_IN h' x \<le> weight \<Gamma> x" for x using currentD_weight_IN[OF h', of x]
      by(auto split: split_indicator_asm elim: order_trans intro: )
    show "h' e = 0" if "e \<notin> \<^bold>E" for e using currentD_outside'[OF h', of e] that by auto
  qed
  moreover have "wave \<Gamma> h'"
  proof
    have "separating (\<Gamma>' 0) T" unfolding T_def by(rule waveD_separating[OF w\<omega>])
    hence "separating \<Gamma> T" by(simp add: separating_gen.simps)
    hence *: "separating \<Gamma> (\<E> T)" by(rule separating_essential)
    show "separating \<Gamma> (TER h')"
    proof
      fix x p y
      assume x: "x \<in> A \<Gamma>" and p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
      from p x y disjoint have py: "p = [y]"
        by(cases)(auto 4 3 elim: rtrancl_path.cases dest: bipartite_E)
      from separatingD[OF * p x y] py have "x \<in> \<E> T \<or> y \<in> \<E> T" by auto
      then show "(\<exists>z\<in>set p. z \<in> TER h') \<or> x \<in> TER h'"
      proof cases
        case left
        then have "x \<notin> \<^bold>V\<^bsub>\<Gamma>_h\<^esub>" using x disjoint
          by(auto 4 4 dest!: vertex_\<Gamma>_hD simp add: S_def elim: essentialE_RF intro!: roofed_greaterI dest: roofedD)
        hence "d_OUT h' x = 0" by(intro currentD_outside_OUT[OF h'])
        with x have "x \<in> TER h'" by(auto simp add: SAT.A SINK.simps)
        thus ?thesis ..
      next
        case right
        have "y \<in> SAT \<Gamma> h'"
        proof(cases "weight \<Gamma> y > 0")
          case True
          with py x y right have "vertex \<Gamma>_h y" by(auto intro: B_vertex)
          hence "y \<in> SAT \<Gamma>_h h'" using B_SAT' right y by auto
          with right y disjoint show ?thesis
            by(auto simp add: currentD_SAT[OF h'] currentD_SAT[OF h''] S_def)
        qed(auto simp add: SAT.simps)
        with currentD_OUT[OF h', of y] y right have "y \<in> TER h'" by(auto simp add: SINK)
        thus ?thesis using py by simp
      qed
    qed
  qed(rule h'')
  ultimately have "h' = zero_current" by(rule looseD_wave[OF loose])
  hence "d_IN h' b = 0" by simp
  moreover from essential b b_V B_SAT' have "b \<in> SAT \<Gamma>_h h'" by(auto)
  ultimately show False using wb b essential disjoint by(auto simp add: SAT.simps S_def)
qed

end

subsection \<open>Single-vertex saturation in unhindered bipartite webs\<close>

text \<open>
  The proof of lemma 6.10 in @{cite "AharoniBergerGeorgakopoulusPerlsteinSpruessel2011JCT"} is flawed.
  The transfinite steps (taking the least upper bound) only preserves unhinderedness, but not looseness.
  However, the single steps to non-limit ordinals assumes that \<open>\<Omega> - f\<^sub>i\<close> is loose in order to
  apply Lemma 6.9.

  Counterexample: The bipartite web with three nodes \<open>a\<^sub>1\<close>, \<open>a\<^sub>2\<close>, \<open>a\<^sub>3\<close> in \<open>A\<close>
  and two nodes \<open>b\<^sub>1\<close>, \<open>b\<^sub>2\<close> in \<open>B\<close> and edges \<open>(a\<^sub>1, b\<^sub>1)\<close>, \<open>(a\<^sub>2, b\<^sub>1)\<close>,
  \<open>(a\<^sub>2, b\<^sub>2)\<close>, \<open>(a\<^sub>3, b\<^sub>2)\<close> and weights \<open>a\<^sub>1 = a\<^sub>3 = 1\<close> and \<open>a\<^sub>2 = 2\<close> and
  \<open>b\<^sub>1 = 3\<close> and \<open>b\<^sub>2 = 2\<close>.
  Then, we can get a sequence of weight reductions on \<open>b\<^sub>2\<close> from \<open>2\<close> to \<open>1.5\<close>,
  \<open>1.25\<close>, \<open>1.125\<close>, etc. with limit \<open>1\<close>.
  All maximal waves in the restricted webs in the sequence are @{term [source] zero_current}, so in
  the limit, we get \<open>k = 0\<close> and \<open>\<epsilon> = 1\<close> for \<open>a\<^sub>2\<close> and \<open>b\<^sub>2\<close>. Now, the
  restricted web for the two is not loose because it contains the wave which assigns 1 to \<open>(a\<^sub>3, b\<^sub>2)\<close>.

  We prove a stronger version which only assumes and ensures on unhinderedness.
\<close>
context countable_bipartite_web begin

lemma web_flow_iff: "web_flow \<Gamma> f \<longleftrightarrow> current \<Gamma> f"
using bipartite_V by(auto simp add: web_flow.simps)

lemma countable_bipartite_web_minus_web:
  assumes f: "current \<Gamma> f"
  shows "countable_bipartite_web (\<Gamma> \<ominus> f)"
using bipartite_V A_vertex bipartite_E disjoint currentD_finite_OUT[OF f] currentD_weight_OUT[OF f] currentD_weight_IN[OF f] currentD_outside_OUT[OF f] currentD_outside_IN[OF f]
by unfold_locales (auto simp add:  weight_outside)

lemma current_plus_current_minus:
  assumes f: "current \<Gamma> f"
  and g: "current (\<Gamma> \<ominus> f) g"
  shows "current \<Gamma> (plus_current f g)" (is "current _ ?fg")
proof
  interpret \<Gamma>: countable_bipartite_web "\<Gamma> \<ominus> f" using f by(rule countable_bipartite_web_minus_web)
  show "d_OUT ?fg x \<le> weight \<Gamma> x" for x
    using currentD_weight_OUT[OF g, of x] currentD_OUT[OF g, of x] currentD_finite_OUT[OF f, of x] currentD_OUT[OF f, of x] currentD_outside_IN[OF f, of x] currentD_outside_OUT[OF f, of x] currentD_weight_OUT[OF f, of x]
    by(cases "x \<in> A \<Gamma> \<or> x \<in> B \<Gamma>")(auto simp add: add.commute d_OUT_def nn_integral_add not_vertex ennreal_le_minus_iff split: if_split_asm)
  show "d_IN ?fg x \<le> weight \<Gamma> x" for x
    using currentD_weight_IN[OF g, of x] currentD_IN[OF g, of x] currentD_finite_IN[OF f, of x] currentD_OUT[OF f, of x] currentD_outside_IN[OF f, of x] currentD_outside_OUT[OF f, of x] currentD_weight_IN[OF f, of x]
    by(cases "x \<in> A \<Gamma> \<or> x \<in> B \<Gamma>")(auto simp add: add.commute  d_IN_def nn_integral_add not_vertex ennreal_le_minus_iff split: if_split_asm)
  show "?fg e = 0" if "e \<notin> \<^bold>E" for e using that currentD_outside'[OF f, of e] currentD_outside'[OF g, of e] by(cases e) simp
qed

lemma wave_plus_current_minus:
  assumes f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  and g: "current (\<Gamma> \<ominus> f) g"
  and w': "wave (\<Gamma> \<ominus> f) g"
  shows "wave \<Gamma> (plus_current f g)" (is "wave _ ?fg")
proof
  show fg: "current \<Gamma> ?fg" using f g by(rule current_plus_current_minus)
  show sep: "separating \<Gamma> (TER ?fg)"
  proof
    fix x p y
    assume x: "x \<in> A \<Gamma>" and p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
    from p x y disjoint have py: "p = [y]"
      by(cases)(auto 4 3 elim: rtrancl_path.cases dest: bipartite_E)
    with waveD_separating[THEN separatingD, OF w p x y] have "x \<in> TER f \<or> y \<in> TER f" by auto
    thus "(\<exists>z\<in>set p. z \<in> TER ?fg) \<or> x \<in> TER ?fg"
    proof cases
      case right
      with y disjoint have "y \<in> TER ?fg" using currentD_OUT[OF fg y]
        by(auto simp add: SAT.simps SINK.simps d_IN_def nn_integral_add not_le add_increasing2)
      thus ?thesis using py by simp
    next
      case x': left
      from p have "path (\<Gamma> \<ominus> f) x p y" by simp
      from waveD_separating[THEN separatingD, OF w' this] x y py
      have "x \<in> TER\<^bsub>\<Gamma> \<ominus> f\<^esub> g \<or> y \<in> TER\<^bsub>\<Gamma> \<ominus> f\<^esub> g" by auto
      thus ?thesis
      proof cases
        case left
        hence "x \<in> TER ?fg" using x x'
          by(auto simp add: SAT.simps SINK.simps d_OUT_def nn_integral_add)
        thus ?thesis ..
      next
        case right
        hence "y \<in> TER ?fg" using disjoint y currentD_OUT[OF fg y] currentD_OUT[OF f y] currentD_finite_IN[OF f, of y]
          by(auto simp add: add.commute SINK.simps SAT.simps d_IN_def nn_integral_add ennreal_minus_le_iff split: if_split_asm)
        with py show ?thesis by auto
      qed
    qed
  qed
qed

lemma minus_plus_current:
  assumes f: "current \<Gamma> f"
  and g: "current (\<Gamma> \<ominus> f) g"
  shows "\<Gamma> \<ominus> plus_current f g = \<Gamma> \<ominus> f \<ominus> g" (is "?lhs = ?rhs")
proof(rule web.equality)
  have "weight ?lhs x = weight ?rhs x" for x
    using currentD_weight_IN[OF f, of x] currentD_weight_IN[OF g, of x]
    by (auto simp add: d_IN_def d_OUT_def nn_integral_add diff_add_eq_diff_diff_swap_ennreal add_increasing2 diff_add_assoc2_ennreal add.assoc)
  thus "weight ?lhs = weight ?rhs" ..
qed simp_all

lemma unhindered_minus_web:
  assumes unhindered: "\<not> hindered \<Gamma>"
  and f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  shows "\<not> hindered (\<Gamma> \<ominus> f)"
proof
  assume "hindered (\<Gamma> \<ominus> f)"
  then obtain g where g: "current (\<Gamma> \<ominus> f) g"
    and w': "wave (\<Gamma> \<ominus> f) g"
    and hind: "hindrance (\<Gamma> \<ominus> f) g" by cases
  let ?fg = "plus_current f g"
  have fg: "current \<Gamma> ?fg" using f g by(rule current_plus_current_minus)
  moreover have "wave \<Gamma> ?fg" using f w g w' by(rule wave_plus_current_minus)
  moreover from hind obtain a where a: "a \<in> A \<Gamma>" and n\<E>: "a \<notin> \<E>\<^bsub>\<Gamma> \<ominus> f\<^esub> (TER\<^bsub>\<Gamma> \<ominus> f\<^esub> g)"
    and wa: "d_OUT g a < weight (\<Gamma> \<ominus> f) a" by cases auto
  from a have "hindrance \<Gamma> ?fg"
  proof
    show "a \<notin> \<E> (TER ?fg)"
    proof
      assume \<E>: "a \<in> \<E> (TER ?fg)"
      then obtain p y where p: "path \<Gamma> a p y" and y: "y \<in> B \<Gamma>"
        and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER ?fg)" by(rule \<E>_E_RF) blast
      from p a y disjoint have py: "p = [y]"
        by(cases)(auto 4 3 elim: rtrancl_path.cases dest: bipartite_E)
      from bypass[of y] py have "y \<notin> TER ?fg" by(auto intro: roofed_greaterI)
      with currentD_OUT[OF fg y] have "y \<notin> SAT \<Gamma> ?fg" by(auto simp add: SINK.simps)
      hence "y \<notin> SAT (\<Gamma> \<ominus> f) g" using y currentD_OUT[OF f y] currentD_finite_IN[OF f, of y]
        by(auto simp add: SAT.simps d_IN_def nn_integral_add ennreal_minus_le_iff add.commute)
      hence "essential (\<Gamma> \<ominus> f) (B (\<Gamma> \<ominus> f)) (TER\<^bsub>\<Gamma> \<ominus> f\<^esub> g) a" using p py y
        by(auto intro!: essentialI)
      moreover from \<E> a have "a \<in> TER\<^bsub>\<Gamma> \<ominus> f\<^esub> g"
        by(auto simp add: SAT.A SINK_plus_current)
      ultimately have "a \<in> \<E>\<^bsub>\<Gamma> \<ominus> f\<^esub> (TER\<^bsub>\<Gamma> \<ominus> f\<^esub> g)" by blast
      thus False using n\<E> by contradiction
    qed
    show "d_OUT ?fg a < weight \<Gamma> a" using a wa currentD_finite_OUT[OF f, of a]
      by(simp add: d_OUT_def less_diff_eq_ennreal less_top add.commute nn_integral_add)
  qed
  ultimately have "hindered \<Gamma>" by(blast intro: hindered.intros)
  with unhindered show False by contradiction
qed

lemma loose_minus_web:
  assumes unhindered: "\<not> hindered \<Gamma>"
  and f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  and maximal: "\<And>w. \<lbrakk> current \<Gamma> w; wave \<Gamma> w; f \<le> w \<rbrakk> \<Longrightarrow> f = w"
  shows "loose (\<Gamma> \<ominus> f)" (is "loose ?\<Gamma>")
proof
  fix g
  assume g: "current ?\<Gamma> g" and w': "wave ?\<Gamma> g"
  let ?g = "plus_current f g"
  from f g have "current \<Gamma> ?g" by(rule current_plus_current_minus)
  moreover from f w g w' have "wave \<Gamma> ?g" by(rule wave_plus_current_minus)
  moreover have "f \<le> ?g" by(clarsimp simp add: le_fun_def)
  ultimately have eq: "f = ?g" by(rule maximal)
  have "g e = 0" for e
  proof(cases e)
    case (Pair x y)
    have "f e \<le> d_OUT f x" unfolding d_OUT_def Pair by(rule nn_integral_ge_point) simp
    also have "\<dots> \<le> weight \<Gamma> x" by(rule currentD_weight_OUT[OF f])
    also have "\<dots> < \<top>" by(simp add: less_top[symmetric])
    finally show "g e = 0" using Pair eq[THEN fun_cong, of e]
      by(cases "f e" "g e" rule: ennreal2_cases)(simp_all add: fun_eq_iff)
  qed
  thus "g = (\<lambda>_. 0)" by(simp add: fun_eq_iff)
next
  show "\<not> hindrance ?\<Gamma> zero_current" using unhindered
  proof(rule contrapos_nn)
    assume "hindrance ?\<Gamma> zero_current"
    then obtain x where a: "x \<in> A ?\<Gamma>" and \<E>: "x \<notin> \<E>\<^bsub>?\<Gamma>\<^esub> (TER\<^bsub>?\<Gamma>\<^esub> zero_current)"
      and weight: "d_OUT zero_current x < weight ?\<Gamma> x" by cases
    have "hindrance \<Gamma> f"
    proof
      show a': "x \<in> A \<Gamma>" using a by simp
      with weight show "d_OUT f x < weight \<Gamma> x"
        by(simp add: less_diff_eq_ennreal less_top[symmetric] currentD_finite_OUT[OF f])
      show "x \<notin> \<E> (TER f)"
      proof
        assume "x \<in> \<E> (TER f)"
        then obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
          and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER f)" by(rule \<E>_E_RF) auto
        from p a' y disjoint have py: "p = [y]"
          by(cases)(auto 4 3 elim: rtrancl_path.cases dest: bipartite_E)
        hence "y \<notin> (TER f)" using bypass[of y] by(auto intro: roofed_greaterI)
        hence "weight ?\<Gamma> y > 0" using currentD_OUT[OF f y] disjoint y
          by(auto simp add: SINK.simps SAT.simps diff_gr0_ennreal)
        hence "y \<notin> TER\<^bsub>?\<Gamma>\<^esub> zero_current" using y disjoint by(auto)
        hence "essential ?\<Gamma> (B ?\<Gamma>) (TER\<^bsub>?\<Gamma>\<^esub> zero_current) x" using p y py by(auto intro!: essentialI)
        with a have "x \<in> \<E>\<^bsub>?\<Gamma>\<^esub> (TER\<^bsub>?\<Gamma>\<^esub> zero_current)" by simp
        with \<E> show False by contradiction
      qed
    qed
    thus "hindered \<Gamma>" using f w ..
  qed
qed

lemma weight_minus_web:
  assumes f: "current \<Gamma> f"
  shows "weight (\<Gamma> \<ominus> f) x = (if x \<in> A \<Gamma> then weight \<Gamma> x - d_OUT f x else weight \<Gamma> x - d_IN f x)"
proof(cases "x \<in> B \<Gamma>")
  case True
  with currentD_OUT[OF f True] disjoint show ?thesis by auto
next
  case False
  hence "d_IN f x = 0" "d_OUT f x = 0" if "x \<notin> A \<Gamma>"
    using currentD_outside_OUT[OF f, of x] currentD_outside_IN[OF f, of x] bipartite_V that by auto
  then show ?thesis by simp
qed


lemma (in -) separating_minus_web [simp]: "separating_gen (G \<ominus> f) = separating_gen G"
by(simp add: separating_gen.simps fun_eq_iff)

lemma current_minus:
  assumes f: "current \<Gamma> f"
  and g: "current \<Gamma> g"
  and le: "\<And>e. g e \<le> f e"
  shows "current (\<Gamma> \<ominus> g) (f - g)"
proof -
  interpret \<Gamma>: countable_bipartite_web "\<Gamma> \<ominus> g" using g by(rule countable_bipartite_web_minus_web)
  note [simp del] = minus_web_sel(2)
    and [simp] = weight_minus_web[OF g]
  show ?thesis
  proof
    show "d_OUT (f - g) x \<le> weight (\<Gamma> \<ominus> g) x" for x unfolding fun_diff_def
      using currentD_weight_OUT[OF f, of x] currentD_weight_IN[OF g, of x]
      by(subst d_OUT_diff)(simp_all add: le currentD_finite_OUT[OF g] currentD_OUT'[OF f] currentD_OUT'[OF g] ennreal_minus_mono)
    show "d_IN (f - g) x \<le> weight (\<Gamma> \<ominus> g) x" for x unfolding fun_diff_def
      using currentD_weight_IN[OF f, of x] currentD_weight_OUT[OF g, of x]
      by(subst d_IN_diff)(simp_all add: le currentD_finite_IN[OF g] currentD_IN[OF f] currentD_IN[OF g] ennreal_minus_mono)
    show "(f - g) e = 0" if "e \<notin> \<^bold>E\<^bsub>\<Gamma> \<ominus> g\<^esub>" for e using that currentD_outside'[OF f] currentD_outside'[OF g] by simp
  qed
qed

lemma
  assumes w: "wave \<Gamma> f"
  and g: "current \<Gamma> g"
  and le: "\<And>e. g e \<le> f e"
  shows wave_minus: "wave (\<Gamma> \<ominus> g) (f - g)"
  and TER_minus: "TER f \<subseteq> TER\<^bsub>\<Gamma> \<ominus> g\<^esub> (f - g)"
proof
  have "x \<in> SINK f \<Longrightarrow> x \<in> SINK (f - g)" for x using d_OUT_mono[of g _ f, OF le, of x]
    by(auto simp add: SINK.simps fun_diff_def d_OUT_diff le currentD_finite_OUT[OF g])
  moreover have "x \<in> SAT \<Gamma> f \<Longrightarrow> x \<in> SAT (\<Gamma> \<ominus> g) (f - g)" for x
    by(auto simp add: SAT.simps currentD_OUT'[OF g] fun_diff_def d_IN_diff le currentD_finite_IN[OF g] ennreal_minus_mono)
  ultimately show TER: "TER f \<subseteq> TER\<^bsub>\<Gamma> \<ominus> g\<^esub> (f - g)" by(auto)

  from w have "separating \<Gamma> (TER f)" by(rule waveD_separating)
  thus "separating (\<Gamma> \<ominus> g) (TER\<^bsub>\<Gamma> \<ominus> g\<^esub> (f - g))" using TER by(simp add: separating_weakening)

  fix x
  assume "x \<notin> RF\<^bsub>\<Gamma> \<ominus> g\<^esub> (TER\<^bsub>\<Gamma> \<ominus> g\<^esub> (f - g))"
  hence "x \<notin> RF (TER f)" using TER by(auto intro: in_roofed_mono)
  hence "d_OUT f x = 0" by(rule waveD_OUT[OF w])
  moreover have "0 \<le> f e" for e using le[of e] by simp
  ultimately show "d_OUT (f - g) x = 0" unfolding d_OUT_def
    by(simp add: nn_integral_0_iff emeasure_count_space_eq_0)
qed

lemma (in -) essential_minus_web [simp]: "essential (\<Gamma> \<ominus> f) = essential \<Gamma>"
by(simp add: essential_def fun_eq_iff)

lemma (in -) RF_in_essential: fixes B shows "essential \<Gamma> B S x \<Longrightarrow> x \<in> roofed_gen \<Gamma> B S \<longleftrightarrow> x \<in> S"
by(auto intro: roofed_greaterI elim!: essentialE_RF dest: roofedD)

lemma (in -) d_OUT_fun_upd:
  assumes "f (x, y) \<noteq> \<top>" "f (x, y) \<ge> 0" "k \<noteq> \<top>" "k \<ge> 0"
  shows "d_OUT (f((x, y) := k)) x' = (if x = x' then d_OUT f x - f (x, y) + k else d_OUT f x')"
  (is "?lhs = ?rhs")
proof(cases "x = x'")
  case True
  have "?lhs = (\<Sum>\<^sup>+ y'. f (x, y') + k * indicator {y} y') - (\<Sum>\<^sup>+ y'. f (x, y') * indicator {y} y')"
    unfolding d_OUT_def using assms True
    by(subst nn_integral_diff[symmetric])
      (auto intro!: nn_integral_cong simp add: AE_count_space split: split_indicator)
  also have "(\<Sum>\<^sup>+ y'. f (x, y') + k * indicator {y} y') = d_OUT f x + (\<Sum>\<^sup>+ y'. k * indicator {y} y')"
    unfolding d_OUT_def using assms
    by(subst nn_integral_add[symmetric])
      (auto intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> - (\<Sum>\<^sup>+ y'. f (x, y') * indicator {y} y') = ?rhs" using True assms
    by(subst diff_add_assoc2_ennreal[symmetric])(auto simp add: d_OUT_def intro!: nn_integral_ge_point)
  finally show ?thesis .
qed(simp add: d_OUT_def)

lemma unhindered_saturate1: \<comment> \<open>Lemma 6.10\<close>
  assumes unhindered: "\<not> hindered \<Gamma>"
  and a: "a \<in> A \<Gamma>"
  shows "\<exists>f. current \<Gamma> f \<and> d_OUT f a = weight \<Gamma> a \<and> \<not> hindered (\<Gamma> \<ominus> f)"
proof -
  from a A_vertex have a_vertex: "vertex \<Gamma> a" by auto
  from unhindered have "\<not> hindrance \<Gamma> zero_current" by(auto intro!: hindered.intros simp add: )
  then have a_\<E>: "a \<in> \<E> (A \<Gamma>)" if "weight \<Gamma> a > 0"
  proof(rule contrapos_np)
    assume "a \<notin> \<E> (A \<Gamma>)"
    with a have "\<not> essential \<Gamma> (B \<Gamma>) (A \<Gamma>) a" by simp
    hence "\<not> essential \<Gamma> (B \<Gamma>) (A \<Gamma> \<union> {x. weight \<Gamma> x \<le> 0}) a"
      by(rule contrapos_nn)(erule essential_mono; simp)
    with a that show "hindrance \<Gamma> zero_current" by(auto intro: hindrance)
  qed

  define F where "F = (\<lambda>(\<epsilon>, h :: 'v current). plus_current \<epsilon> h)"
  have F_simps: "F (\<epsilon>, h) = plus_current \<epsilon> h" for \<epsilon> h by(simp add: F_def)
  define Fld where "Fld = {(\<epsilon>, h).
     current \<Gamma> \<epsilon> \<and> (\<forall>x. x \<noteq> a \<longrightarrow> d_OUT \<epsilon> x = 0) \<and>
     current (\<Gamma> \<ominus> \<epsilon>) h \<and> wave (\<Gamma> \<ominus> \<epsilon>) h \<and>
     \<not> hindered (\<Gamma> \<ominus> F (\<epsilon>, h))}"
  define leq where "leq = restrict_rel Fld {(f, f'). f \<le> f'}"
  have Fld: "Field leq = Fld" by(auto simp add: leq_def)
  have F_I [intro?]: "(\<epsilon>, h) \<in> Field leq"
    if "current \<Gamma> \<epsilon>" and "\<And>x. x \<noteq> a \<Longrightarrow> d_OUT \<epsilon> x = 0"
    and "current (\<Gamma> \<ominus> \<epsilon>) h" and "wave (\<Gamma> \<ominus> \<epsilon>) h"
    and "\<not> hindered (\<Gamma> \<ominus> F (\<epsilon>, h))"
    for \<epsilon> h using that by(simp add: Fld Fld_def)
  have \<epsilon>_curr: "current \<Gamma> \<epsilon>" if "(\<epsilon>, h) \<in> Field leq" for \<epsilon> h using that by(simp add: Fld Fld_def)
  have OUT_\<epsilon>: "\<And>x. x \<noteq> a \<Longrightarrow> d_OUT \<epsilon> x = 0" if "(\<epsilon>, h) \<in> Field leq" for \<epsilon> h using that by(simp add: Fld Fld_def)
  have h: "current (\<Gamma> \<ominus> \<epsilon>) h" if "(\<epsilon>, h) \<in> Field leq" for \<epsilon> h using that by(simp add: Fld Fld_def)
  have h_w: "wave (\<Gamma> \<ominus> \<epsilon>) h" if "(\<epsilon>, h) \<in> Field leq" for \<epsilon> h using that by(simp add: Fld Fld_def)
  have unhindered': "\<not> hindered (\<Gamma> \<ominus> F \<epsilon>h)" if "\<epsilon>h \<in> Field leq" for \<epsilon>h using that by(simp add: Fld Fld_def split: prod.split_asm)
  have f: "current \<Gamma> (F \<epsilon>h)" if "\<epsilon>h \<in> Field leq" for \<epsilon>h using \<epsilon>_curr h that
    by(cases \<epsilon>h)(simp add: F_simps current_plus_current_minus)
  have out_\<epsilon>: "\<epsilon> (x, y) = 0" if "(\<epsilon>, h) \<in> Field leq" "x \<noteq> a" for \<epsilon> h x y
  proof(rule antisym)
    have "\<epsilon> (x, y) \<le> d_OUT \<epsilon> x" unfolding d_OUT_def by(rule nn_integral_ge_point) simp
    with OUT_\<epsilon>[OF that] show "\<epsilon> (x, y) \<le> 0" by simp
  qed simp
  have IN_\<epsilon>: "d_IN \<epsilon> x = \<epsilon> (a, x)" if "(\<epsilon>, h) \<in> Field leq" for \<epsilon> h x
  proof(rule trans)
    show "d_IN \<epsilon> x = (\<Sum>\<^sup>+ y. \<epsilon> (y, x) * indicator {a} y)" unfolding d_IN_def
      by(rule nn_integral_cong)(simp add: out_\<epsilon>[OF that] split: split_indicator)
  qed(simp add: max_def \<epsilon>_curr[OF that])
  have leqI: "((\<epsilon>, h), (\<epsilon>', h')) \<in> leq" if "\<epsilon> \<le> \<epsilon>'" "h \<le> h'" "(\<epsilon>, h) \<in> Field leq" "(\<epsilon>', h') \<in> Field leq" for \<epsilon> h \<epsilon>' h'
    using that unfolding Fld by(simp add: leq_def in_restrict_rel_iff)

  have chain_Field: "Sup M \<in> Field leq" if M: "M \<in> Chains leq" and nempty: "M \<noteq> {}" for M
    unfolding Sup_prod_def
  proof
    from nempty obtain \<epsilon> h where in_M: "(\<epsilon>, h) \<in> M" by auto
    with M have Field: "(\<epsilon>, h) \<in> Field leq" by(rule Chains_FieldD)

    from M have chain: "Complete_Partial_Order.chain (\<lambda>\<epsilon> \<epsilon>'. (\<epsilon>, \<epsilon>') \<in> leq) M"
      by(intro Chains_into_chain) simp
    hence chain': "Complete_Partial_Order.chain (\<le>) M"
      by(auto simp add: chain_def leq_def in_restrict_rel_iff)
    hence chain1: "Complete_Partial_Order.chain (\<le>) (fst ` M)"
      and chain2: "Complete_Partial_Order.chain (\<le>) (snd ` M)"
      by(rule chain_imageI; auto)+

    have outside1: "Sup (fst ` M) (x, y) = 0" if "\<not> edge \<Gamma> x y" for x y using that
      by(auto intro!: SUP_eq_const simp add: nempty dest!: Chains_FieldD[OF M] \<epsilon>_curr currentD_outside)
    then have "support_flow (Sup (fst ` M)) \<subseteq> \<^bold>E" by(auto elim!: support_flow.cases intro: ccontr)
    hence supp_flow1: "countable (support_flow (Sup (fst ` M)))" by(rule countable_subset) simp

    show SM1: "current \<Gamma> (Sup (fst ` M))"
      by(rule current_Sup[OF chain1 _ _ supp_flow1])(auto dest: Chains_FieldD[OF M, THEN \<epsilon>_curr] simp add: nempty)
    show OUT1_na: "d_OUT (Sup (fst ` M)) x = 0" if "x \<noteq> a" for x using that
      by(subst d_OUT_Sup[OF chain1 _ supp_flow1])(auto simp add: nempty intro!: SUP_eq_const dest: Chains_FieldD[OF M, THEN OUT_\<epsilon>])

    interpret SM1: countable_bipartite_web "\<Gamma> \<ominus> Sup (fst ` M)"
      using SM1 by(rule countable_bipartite_web_minus_web)

    let ?h = "Sup (snd ` M)"
    have outside2: "?h (x, y) = 0" if "\<not> edge \<Gamma> x y" for x y using that
      by(auto intro!: SUP_eq_const simp add: nempty dest!: Chains_FieldD[OF M] h currentD_outside)
    then have "support_flow ?h \<subseteq> \<^bold>E" by(auto elim!: support_flow.cases intro: ccontr)
    hence supp_flow2: "countable (support_flow ?h)" by(rule countable_subset) simp

    have OUT1: "d_OUT (Sup (fst ` M)) x = (SUP (\<epsilon>, h)\<in>M. d_OUT \<epsilon> x)" for x
      by (subst d_OUT_Sup [OF chain1 _ supp_flow1])
        (simp_all add: nempty split_beta image_comp)
    have OUT1': "d_OUT (Sup (fst ` M)) x = (if x = a then SUP (\<epsilon>, h)\<in>M. d_OUT \<epsilon> a else 0)" for x
      unfolding OUT1 by(auto intro!: SUP_eq_const simp add: nempty OUT_\<epsilon> dest!: Chains_FieldD[OF M])
    have OUT1_le: "(\<Squnion>\<epsilon>h\<in>M. d_OUT (fst \<epsilon>h) x) \<le> weight \<Gamma> x" for x
      using currentD_weight_OUT[OF SM1, of x] OUT1[of x] by(simp add: split_beta)
    have OUT1_nonneg: "0 \<le> (\<Squnion>\<epsilon>h\<in>M. d_OUT (fst \<epsilon>h) x)" for x using in_M by(rule SUP_upper2)(simp add: )
    have IN1: "d_IN (Sup (fst ` M)) x = (SUP (\<epsilon>, h)\<in>M. d_IN \<epsilon> x)" for x
      by (subst d_IN_Sup [OF chain1 _ supp_flow1])
        (simp_all add: nempty split_beta image_comp)
    have IN1_le: "(\<Squnion>\<epsilon>h\<in>M. d_IN (fst \<epsilon>h) x) \<le> weight \<Gamma> x" for x
      using currentD_weight_IN[OF SM1, of x] IN1[of x] by(simp add: split_beta)
    have IN1_nonneg: "0 \<le> (\<Squnion>\<epsilon>h\<in>M. d_IN (fst \<epsilon>h) x)" for x using in_M by(rule SUP_upper2) simp
    have IN1': "d_IN (Sup (fst ` M)) x = (SUP (\<epsilon>, h)\<in>M. \<epsilon> (a, x))" for x
      unfolding IN1 by(rule SUP_cong[OF refl])(auto dest!: Chains_FieldD[OF M] IN_\<epsilon>)

    have directed: "\<exists>\<epsilon>k''\<in>M. F (snd \<epsilon>k) + F (fst \<epsilon>k') \<le> F (snd \<epsilon>k'') + F (fst \<epsilon>k'')"
      if mono: "\<And>f g. (\<And>z. f z \<le> g z) \<Longrightarrow> F f \<le> F g" "\<epsilon>k \<in> M" "\<epsilon>k' \<in> M"
      for \<epsilon>k \<epsilon>k' and F :: "_ \<Rightarrow> ennreal"
      using chainD[OF chain that(2-3)]
    proof cases
      case left
      hence "snd \<epsilon>k \<le> snd \<epsilon>k'" by(simp add: leq_def less_eq_prod_def in_restrict_rel_iff)
      hence "F (snd \<epsilon>k) + F (fst \<epsilon>k') \<le> F (snd \<epsilon>k') + F (fst \<epsilon>k')"
        by(intro add_right_mono mono)(clarsimp simp add: le_fun_def)
      with that show ?thesis by blast
    next
      case right
      hence "fst \<epsilon>k' \<le> fst \<epsilon>k" by(simp add: leq_def less_eq_prod_def in_restrict_rel_iff)
      hence "F (snd \<epsilon>k) + F (fst \<epsilon>k') \<le> F (snd \<epsilon>k) + F (fst \<epsilon>k)"
        by(intro add_left_mono mono)(clarsimp simp add: le_fun_def)
      with that show ?thesis by blast
    qed
    have directed_OUT: "\<exists>\<epsilon>k''\<in>M. d_OUT (snd \<epsilon>k) x + d_OUT (fst \<epsilon>k') x \<le> d_OUT (snd \<epsilon>k'') x + d_OUT (fst \<epsilon>k'') x"
      if "\<epsilon>k \<in> M" "\<epsilon>k' \<in> M" for x \<epsilon>k \<epsilon>k' by(rule directed; rule d_OUT_mono that)
    have directed_IN: "\<exists>\<epsilon>k''\<in>M. d_IN (snd \<epsilon>k) x + d_IN (fst \<epsilon>k') x \<le> d_IN (snd \<epsilon>k'') x + d_IN (fst \<epsilon>k'') x"
      if "\<epsilon>k \<in> M" "\<epsilon>k' \<in> M" for x \<epsilon>k \<epsilon>k' by(rule directed; rule d_IN_mono that)

    let ?\<Gamma> = "\<Gamma> \<ominus> Sup (fst ` M)"

    have hM2: "current ?\<Gamma> h" if \<epsilon>h: "(\<epsilon>, h) \<in> M" for \<epsilon> h
    proof
      from \<epsilon>h have Field: "(\<epsilon>, h) \<in> Field leq" by(rule Chains_FieldD[OF M])
      then have H: "current (\<Gamma> \<ominus> \<epsilon>) h" and \<epsilon>_curr': "current \<Gamma> \<epsilon>" by(rule h \<epsilon>_curr)+
      from \<epsilon>_curr' interpret \<Gamma>: countable_bipartite_web "\<Gamma> \<ominus> \<epsilon>" by(rule countable_bipartite_web_minus_web)

      fix x
      have "d_OUT h x \<le> d_OUT ?h x" using \<epsilon>h by(intro d_OUT_mono)(auto intro: SUP_upper2)
      also have OUT: "\<dots> = (SUP h\<in>snd ` M. d_OUT h x)" using chain2 _ supp_flow2
        by(rule d_OUT_Sup)(simp_all add: nempty)
      also have "\<dots> = \<dots> + (SUP \<epsilon>\<in>fst ` M. d_OUT \<epsilon> x) - (SUP \<epsilon>\<in>fst ` M. d_OUT \<epsilon> x)"
        using OUT1_le[of x]
        by (intro ennreal_add_diff_cancel_right[symmetric] neq_top_trans[OF weight_finite, of _ x])
          (simp add: image_comp)
      also have "\<dots> = (SUP (\<epsilon>, k)\<in>M. d_OUT k x + d_OUT \<epsilon> x) - (SUP \<epsilon>\<in>fst ` M. d_OUT \<epsilon> x)" unfolding split_def
        by (subst SUP_add_directed_ennreal[OF directed_OUT])
          (simp_all add: image_comp)
      also have "(SUP (\<epsilon>, k)\<in>M. d_OUT k x + d_OUT \<epsilon> x) \<le> weight \<Gamma> x"
        apply(clarsimp dest!: Chains_FieldD[OF M] intro!: SUP_least)
        subgoal premises that for \<epsilon> h
          using currentD_weight_OUT[OF h[OF that], of x] currentD_weight_OUT[OF \<epsilon>_curr[OF that], of x]
             countable_bipartite_web_minus_web[OF \<epsilon>_curr, THEN countable_bipartite_web.currentD_OUT', OF that h[OF that], where x=x]
          by (auto simp add: ennreal_le_minus_iff split: if_split_asm)
        done
      also have "(SUP \<epsilon>\<in>fst ` M. d_OUT \<epsilon> x) = d_OUT (Sup (fst ` M)) x" using OUT1
        by (simp add: split_beta image_comp)
      finally show "d_OUT h x \<le> weight ?\<Gamma> x"
        using \<Gamma>.currentD_OUT'[OF h[OF Field], of x] currentD_weight_IN[OF SM1, of x] by(auto simp add: ennreal_minus_mono)

      have "d_IN h x \<le> d_IN ?h x" using \<epsilon>h by(intro d_IN_mono)(auto intro: SUP_upper2)
      also have IN: "\<dots> = (SUP h\<in>snd ` M. d_IN h x)" using chain2 _ supp_flow2
        by(rule d_IN_Sup)(simp_all add: nempty)
      also have "\<dots> = \<dots> + (SUP \<epsilon>\<in>fst ` M. d_IN \<epsilon> x) - (SUP \<epsilon>\<in>fst ` M. d_IN \<epsilon> x)"
        using IN1_le[of x]
        by (intro ennreal_add_diff_cancel_right [symmetric] neq_top_trans [OF weight_finite, of _ x])
          (simp add: image_comp)
      also have "\<dots> = (SUP (\<epsilon>, k)\<in>M. d_IN k x + d_IN \<epsilon> x) - (SUP \<epsilon>\<in>fst ` M. d_IN \<epsilon> x)" unfolding split_def
        by (subst SUP_add_directed_ennreal [OF directed_IN])
          (simp_all add: image_comp)
      also have "(SUP (\<epsilon>, k)\<in>M. d_IN k x + d_IN \<epsilon> x) \<le> weight \<Gamma> x"
        apply(clarsimp dest!: Chains_FieldD[OF M] intro!: SUP_least)
        subgoal premises that for \<epsilon> h
          using currentD_weight_OUT[OF h, OF that, where x=x] currentD_weight_IN[OF h, OF that, where x=x]
            countable_bipartite_web_minus_web[OF \<epsilon>_curr, THEN countable_bipartite_web.currentD_OUT', OF that h[OF that], where x=x]
            currentD_OUT'[OF \<epsilon>_curr, OF that, where x=x] currentD_IN[OF \<epsilon>_curr, OF that, of x] currentD_weight_IN[OF \<epsilon>_curr, OF that, where x=x]
          by (auto simp add: ennreal_le_minus_iff image_comp
                     split: if_split_asm intro: add_increasing2 order_trans [rotated])
        done
      also have "(SUP \<epsilon>\<in>fst ` M. d_IN \<epsilon> x) = d_IN (Sup (fst ` M)) x"
        using IN1 by (simp add: split_beta image_comp)
      finally show "d_IN h x \<le> weight ?\<Gamma> x"
        using currentD_IN[OF h[OF Field], of x] currentD_weight_OUT[OF SM1, of x]
        by(auto simp add: ennreal_minus_mono)
          (auto simp add: ennreal_le_minus_iff add_increasing2)
      show "h e = 0" if "e \<notin> \<^bold>E\<^bsub>?\<Gamma>\<^esub>" for e using currentD_outside'[OF H, of e] that by simp
    qed

    from nempty have "snd ` M \<noteq> {}" by simp
    from chain2 this _ supp_flow2 show current: "current ?\<Gamma> ?h"
      by(rule current_Sup)(clarify; rule hM2; simp)

    have wM: "wave ?\<Gamma> h" if "(\<epsilon>, h) \<in> M" for \<epsilon> h
    proof
      let ?\<Gamma>' = "\<Gamma> \<ominus> \<epsilon>"
      have subset: "TER\<^bsub>?\<Gamma>'\<^esub> h \<subseteq> TER\<^bsub>?\<Gamma>\<^esub> h"
        using currentD_OUT'[OF SM1] currentD_OUT'[OF \<epsilon>_curr[OF Chains_FieldD[OF M that]]] that
        by(auto 4 7 elim!: SAT.cases intro: SAT.intros elim!: order_trans[rotated] intro: ennreal_minus_mono d_IN_mono intro!: SUP_upper2 split: if_split_asm)

      from h_w[OF Chains_FieldD[OF M], OF that] have "separating ?\<Gamma>' (TER\<^bsub>?\<Gamma>'\<^esub> h)" by(rule waveD_separating)
      then show "separating ?\<Gamma> (TER\<^bsub>?\<Gamma>\<^esub> h)" using subset by(auto intro: separating_weakening)
    qed(rule hM2[OF that])
    show wave: "wave ?\<Gamma> ?h" using chain2 \<open>snd ` M \<noteq> {}\<close> _ supp_flow2
      by(rule wave_lub)(clarify; rule wM; simp)

    define f where "f = F (Sup (fst ` M), Sup (snd ` M))"
    have supp_flow: "countable (support_flow f)"
      using supp_flow1 supp_flow2 support_flow_plus_current[of "Sup (fst ` M)" ?h]
      unfolding f_def F_simps by(blast intro: countable_subset)
    have f_alt: "f = Sup ((\<lambda>(\<epsilon>, h). plus_current \<epsilon> h) ` M)"
      apply (simp add: fun_eq_iff split_def f_def nempty F_def image_comp)
      apply (subst (1 2) add.commute)
      apply (subst SUP_add_directed_ennreal)
      apply (rule directed)
      apply (auto dest!: Chains_FieldD [OF M])
      done
    have f_curr: "current \<Gamma> f" unfolding f_def F_simps using SM1 current by(rule current_plus_current_minus)
    have IN_f: "d_IN f x = d_IN (Sup (fst ` M)) x + d_IN (Sup (snd ` M)) x" for x
      unfolding f_def F_simps plus_current_def
      by(rule d_IN_add SM1 current)+
    have OUT_f: "d_OUT f x = d_OUT (Sup (fst ` M)) x + d_OUT (Sup (snd ` M)) x" for x
      unfolding f_def F_simps plus_current_def
      by(rule d_OUT_add SM1 current)+

    show "\<not> hindered (\<Gamma> \<ominus> f)" (is "\<not> hindered ?\<Omega>") \<comment> \<open>Assertion 6.11\<close>
    proof
      assume hindered: "hindered ?\<Omega>"
      then obtain g where g: "current ?\<Omega> g" and g_w: "wave ?\<Omega> g" and hindrance: "hindrance ?\<Omega> g" by cases
      from hindrance obtain z where z: "z \<in> A \<Gamma>" and z\<E>: "z \<notin> \<E>\<^bsub>?\<Omega>\<^esub> (TER\<^bsub>?\<Omega>\<^esub> g)"
        and OUT_z: "d_OUT g z < weight ?\<Omega> z" by cases auto
      define \<delta> where "\<delta> = weight ?\<Omega> z - d_OUT g z"
      have \<delta>_pos: "\<delta> > 0" using OUT_z by(simp add: \<delta>_def diff_gr0_ennreal del: minus_web_sel)
      then have \<delta>_finite[simp]: "\<delta> \<noteq> \<top>" using z
        by(simp_all add: \<delta>_def)

      have "\<exists>(\<epsilon>, h) \<in> M. d_OUT f a < d_OUT (plus_current \<epsilon> h) a + \<delta>"
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence greater: "d_OUT (plus_current \<epsilon> h) a + \<delta> \<le> d_OUT f a" if "(\<epsilon>, h) \<in> M" for \<epsilon> h using that by auto

        have chain'': "Complete_Partial_Order.chain (\<le>) ((\<lambda>(\<epsilon>, h). plus_current \<epsilon> h) ` M)"
          using chain' by(rule chain_imageI)(auto simp add: le_fun_def add_mono)

        have "d_OUT f a + 0 < d_OUT f a + \<delta>"
          using currentD_finite_OUT[OF f_curr, of a] by (simp add: \<delta>_pos)
        also have "d_OUT f a + \<delta> = (SUP (\<epsilon>, h)\<in>M. d_OUT (plus_current \<epsilon> h) a) + \<delta>"
          using chain'' nempty supp_flow
          unfolding f_alt by (subst d_OUT_Sup)
            (simp_all add: plus_current_def [abs_def] split_def image_comp)
        also have "\<dots> \<le> d_OUT f a"
          unfolding ennreal_SUP_add_left[symmetric, OF nempty]
        proof(rule SUP_least, clarify)
          show "d_OUT (plus_current \<epsilon> h) a + \<delta> \<le> d_OUT f a" if "(\<epsilon>, h) \<in> M" for \<epsilon> h
            using greater[OF that] currentD_finite_OUT[OF Chains_FieldD[OF M that, THEN f], of a]
            by(auto simp add: ennreal_le_minus_iff add.commute F_def)
        qed
        finally show False by simp
      qed
      then obtain \<epsilon> h where hM: "(\<epsilon>, h) \<in> M" and close: "d_OUT f a < d_OUT (plus_current \<epsilon> h) a + \<delta>" by blast
      have Field: "(\<epsilon>, h) \<in> Field leq" using hM by(rule Chains_FieldD[OF M])
      then have \<epsilon>: "current \<Gamma> \<epsilon>"
        and unhindered_h: "\<not> hindered (\<Gamma> \<ominus> F (\<epsilon>, h))"
        and h_curr: "current (\<Gamma> \<ominus> \<epsilon>) h"
        and h_w: "wave (\<Gamma> \<ominus> \<epsilon>) h"
        and OUT_\<epsilon>: "x \<noteq> a \<Longrightarrow> d_OUT \<epsilon> x = 0" for x
        by(rule \<epsilon>_curr OUT_\<epsilon> h h_w unhindered')+
      let ?\<epsilon>h = "plus_current \<epsilon> h"
      have \<epsilon>h_curr: "current \<Gamma> ?\<epsilon>h" using Field unfolding F_simps[symmetric] by(rule f)

      interpret h: countable_bipartite_web "\<Gamma> \<ominus> \<epsilon>" using \<epsilon> by(rule countable_bipartite_web_minus_web)
      interpret \<epsilon>h: countable_bipartite_web "\<Gamma> \<ominus> ?\<epsilon>h" using \<epsilon>h_curr by(rule countable_bipartite_web_minus_web)
      note [simp del] = minus_web_sel(2)
        and [simp] = weight_minus_web[OF \<epsilon>h_curr] weight_minus_web[OF SM1, simplified]

      define k where "k e = Sup (fst ` M) e - \<epsilon> e" for e
      have k_simps: "k (x, y) = Sup (fst ` M) (x, y) - \<epsilon> (x, y)" for x y by(simp add: k_def)
      have k_alt: "k (x, y) = (if x = a \<and> edge \<Gamma> x y then Sup (fst ` M) (a, y) - \<epsilon> (a, y) else 0)" for x y
        by (cases "x = a")
          (auto simp add: k_simps out_\<epsilon> [OF Field] currentD_outside [OF \<epsilon>] image_comp
           intro!: SUP_eq_const [OF nempty] dest!: Chains_FieldD [OF M]
           intro: currentD_outside [OF \<epsilon>_curr] out_\<epsilon>)
      have OUT_k: "d_OUT k x = (if x = a then d_OUT (Sup (fst ` M)) a - d_OUT \<epsilon> a else 0)" for x
      proof -
        have "d_OUT k x = (if x = a then (\<Sum>\<^sup>+ y. Sup (fst ` M) (a, y) - \<epsilon> (a, y)) else 0)"
          using currentD_outside[OF SM1] currentD_outside[OF \<epsilon>]
          by(auto simp add: k_alt d_OUT_def intro!: nn_integral_cong)
        also have "(\<Sum>\<^sup>+ y. Sup (fst ` M) (a, y) - \<epsilon> (a, y)) = d_OUT (Sup (fst `M)) a - d_OUT \<epsilon> a"
          using currentD_finite_OUT[OF \<epsilon>, of a] hM unfolding d_OUT_def
          by(subst nn_integral_diff[symmetric])(auto simp add: AE_count_space intro!: SUP_upper2)
        finally show ?thesis .
      qed
      have IN_k: "d_IN k y = (if edge \<Gamma> a y then Sup (fst ` M) (a, y) - \<epsilon> (a, y) else 0)" for y
      proof -
        have "d_IN k y = (\<Sum>\<^sup>+ x. (if edge \<Gamma> x y then Sup (fst ` M) (a, y) - \<epsilon> (a, y) else 0) * indicator {a} x)"
          unfolding d_IN_def by(rule nn_integral_cong)(auto simp add: k_alt outgoing_def split: split_indicator)
        also have "\<dots> = (if edge \<Gamma> a y then Sup (fst ` M) (a, y) - \<epsilon> (a, y) else 0)" using hM
          by(auto simp add: max_def intro!: SUP_upper2)
        finally show ?thesis .
      qed

      have OUT_\<epsilon>h: "d_OUT ?\<epsilon>h x = d_OUT \<epsilon> x + d_OUT h x" for x
        unfolding plus_current_def by(rule d_OUT_add)+
      have IN_\<epsilon>h: "d_IN ?\<epsilon>h x = d_IN \<epsilon> x + d_IN h x" for x
        unfolding plus_current_def by(rule d_IN_add)+

      have OUT1_le': "d_OUT (Sup (fst`M)) x \<le> weight \<Gamma> x" for x
        using OUT1_le[of x] unfolding OUT1 by (simp add: split_beta')

      have k: "current (\<Gamma> \<ominus> ?\<epsilon>h) k"
      proof
        fix x
        show "d_OUT k x \<le> weight (\<Gamma> \<ominus> ?\<epsilon>h) x"
          using a OUT1_na[of x] currentD_weight_OUT[OF hM2[OF hM], of x] currentD_weight_IN[OF \<epsilon>h_curr, of x]
            currentD_weight_IN[OF \<epsilon>, of x] OUT1_le'[of x]
          apply(auto simp add: diff_add_eq_diff_diff_swap_ennreal diff_add_assoc2_ennreal[symmetric]
                               OUT_k OUT_\<epsilon> OUT_\<epsilon>h IN_\<epsilon>h currentD_OUT'[OF \<epsilon>] IN_\<epsilon>[OF Field] h.currentD_OUT'[OF h_curr])
          apply(subst diff_diff_commute_ennreal)
          apply(intro ennreal_minus_mono)
          apply(auto simp add: ennreal_le_minus_iff ac_simps less_imp_le OUT1)
          done

        have *: "(\<Squnion>xa\<in>M. fst xa (a, x)) \<le> d_IN (Sup (fst`M)) x"
          unfolding IN1 by (intro SUP_subset_mono) (auto simp: split_beta' d_IN_ge_point)
        also have "\<dots> \<le> weight \<Gamma> x"
          using IN1_le[of x] IN1 by (simp add: split_beta')
        finally show "d_IN k x \<le> weight (\<Gamma> \<ominus> ?\<epsilon>h) x"
          using currentD_weight_IN[OF \<epsilon>h_curr, of x] currentD_weight_OUT[OF \<epsilon>h_curr, of x]
            currentD_weight_IN[OF hM2[OF hM], of x] IN_\<epsilon>[OF Field, of x] *
          apply (auto simp add: IN_k outgoing_def IN_\<epsilon>h IN_\<epsilon> A_in diff_add_eq_diff_diff_swap_ennreal)
          apply (subst diff_diff_commute_ennreal)
          apply (intro ennreal_minus_mono[OF _ order_refl])
          apply (auto simp add: ennreal_le_minus_iff ac_simps image_comp intro: order_trans add_mono)
          done
        show "k e = 0" if "e \<notin> \<^bold>E\<^bsub>\<Gamma> \<ominus> ?\<epsilon>h\<^esub>" for e
          using that by (cases e) (simp add: k_alt)
      qed

      define q where "q = (\<Sum>\<^sup>+ y\<in>B (\<Gamma> \<ominus> ?\<epsilon>h). d_IN k y - d_OUT k y)"
      have q_alt: "q = (\<Sum>\<^sup>+ y\<in>- A (\<Gamma> \<ominus> ?\<epsilon>h). d_IN k y - d_OUT k y)" using disjoint
        by(auto simp add: q_def nn_integral_count_space_indicator currentD_outside_OUT[OF k] currentD_outside_IN[OF k] not_vertex split: split_indicator intro!: nn_integral_cong)
      have q_simps: "q = d_OUT (Sup (fst ` M)) a - d_OUT \<epsilon> a"
      proof -
        have "q = (\<Sum>\<^sup>+ y. d_IN k y)" using a IN1 OUT1 OUT1_na unfolding q_alt
          by(auto simp add: nn_integral_count_space_indicator OUT_k IN_\<epsilon>[OF Field] OUT_\<epsilon> currentD_outside[OF \<epsilon>] outgoing_def no_loop A_in IN_k intro!: nn_integral_cong split: split_indicator)
        also have "\<dots> = d_OUT (Sup (fst ` M)) a - d_OUT \<epsilon> a" using currentD_finite_OUT[OF \<epsilon>, of a] hM currentD_outside[OF SM1] currentD_outside[OF \<epsilon>]
          by(subst d_OUT_diff[symmetric])(auto simp add: d_OUT_def IN_k intro!: SUP_upper2 nn_integral_cong)
        finally show ?thesis .
      qed
      have q_finite: "q \<noteq> \<top>" using currentD_finite_OUT[OF SM1, of a]
        by(simp add: q_simps)
      have q_nonneg: "0 \<le> q" using hM by(auto simp add: q_simps intro!: d_OUT_mono SUP_upper2)
      have q_less_\<delta>: "q < \<delta>" using close
        unfolding q_simps \<delta>_def OUT_\<epsilon>h OUT_f
      proof -
        let ?F = "d_OUT (Sup (fst`M)) a" and ?S = "d_OUT (Sup (snd`M)) a"
          and ?\<epsilon> = "d_OUT \<epsilon> a" and ?h = "d_OUT h a" and ?w = "weight (\<Gamma> \<ominus> f) z - d_OUT g z"
        have "?F + ?h \<le> ?F + ?S"
          using hM by (auto intro!: add_mono d_OUT_mono SUP_upper2)
        also assume "?F + ?S < ?\<epsilon> + ?h + ?w"
        finally have "?h + ?F < ?h + (?w + ?\<epsilon>)"
          by (simp add: ac_simps)
        then show "?F - ?\<epsilon> < ?w"
          using currentD_finite_OUT[OF \<epsilon>, of a] hM unfolding ennreal_add_left_cancel_less
          by (subst minus_less_iff_ennreal) (auto intro!: d_OUT_mono SUP_upper2 simp: less_top)
      qed

      define g' where "g' = plus_current g (Sup (snd ` M) - h)"
      have g'_simps: "g' e = g e + Sup (snd ` M) e - h e" for e
        using hM by(auto simp add: g'_def intro!: add_diff_eq_ennreal intro: SUP_upper2)
      have OUT_g': "d_OUT g' x = d_OUT g x + (d_OUT (Sup (snd ` M)) x - d_OUT h x)" for x
        unfolding g'_simps[abs_def] using \<epsilon>h.currentD_finite_OUT[OF k] hM h.currentD_finite_OUT[OF h_curr] hM
        apply(subst d_OUT_diff)
         apply(auto simp add: add_diff_eq_ennreal[symmetric] k_simps intro: add_increasing intro!: SUP_upper2)
        apply(subst d_OUT_add)
         apply(auto simp add: add_diff_eq_ennreal[symmetric] k_simps intro: add_increasing intro!:)
        apply(simp add: add_diff_eq_ennreal SUP_apply[abs_def])
        apply(auto simp add: g'_def image_comp intro!: add_diff_eq_ennreal[symmetric] d_OUT_mono intro: SUP_upper2)
        done
      have IN_g': "d_IN g' x = d_IN g x + (d_IN (Sup (snd ` M)) x - d_IN h x)" for x
        unfolding g'_simps[abs_def] using \<epsilon>h.currentD_finite_IN[OF k] hM h.currentD_finite_IN[OF h_curr] hM
        apply(subst d_IN_diff)
         apply(auto simp add: add_diff_eq_ennreal[symmetric] k_simps intro: add_increasing intro!: SUP_upper2)
        apply(subst d_IN_add)
         apply(auto simp add: add_diff_eq_ennreal[symmetric] k_simps intro: add_increasing intro!: SUP_upper)
        apply(auto simp add: g'_def SUP_apply[abs_def] image_comp intro!: add_diff_eq_ennreal[symmetric] d_IN_mono intro: SUP_upper2)
        done

      have h': "current (\<Gamma> \<ominus> Sup (fst ` M)) h" using hM by(rule hM2)

      let ?\<Gamma> = "\<Gamma> \<ominus> ?\<epsilon>h \<ominus> k"
      interpret \<Gamma>: web ?\<Gamma> using k by(rule \<epsilon>h.web_minus_web)
      note [simp] = \<epsilon>h.weight_minus_web[OF k] h.weight_minus_web[OF h_curr]
        weight_minus_web[OF f_curr] SM1.weight_minus_web[OF h', simplified]

      interpret \<Omega>: countable_bipartite_web "\<Gamma> \<ominus> f" using f_curr by(rule countable_bipartite_web_minus_web)

      have *: "\<Gamma> \<ominus> f = \<Gamma> \<ominus> Sup (fst ` M) \<ominus> Sup (snd ` M)" unfolding f_def F_simps
        using SM1 current by(rule minus_plus_current)
      have OUT_\<epsilon>k: "d_OUT (Sup (fst ` M)) x = d_OUT \<epsilon> x + d_OUT k x" for x
        using OUT1'[of x] currentD_finite_OUT[OF \<epsilon>] hM
        by(auto simp add: OUT_k OUT_\<epsilon> add_diff_self_ennreal SUP_upper2)
      have IN_\<epsilon>k: "d_IN (Sup (fst ` M)) x = d_IN \<epsilon> x + d_IN k x" for x
        using IN1'[of x] currentD_finite_IN[OF \<epsilon>] currentD_outside[OF \<epsilon>] currentD_outside[OF \<epsilon>_curr]
        by(auto simp add: IN_k IN_\<epsilon>[OF Field] add_diff_self_ennreal split_beta nempty image_comp
                dest!: Chains_FieldD[OF M] intro!: SUP_eq_const intro: SUP_upper2[OF hM])
      have **: "?\<Gamma> = \<Gamma> \<ominus> Sup (fst ` M) \<ominus> h"
      proof(rule web.equality)
        show "weight ?\<Gamma> = weight (\<Gamma> \<ominus> Sup (fst ` M) \<ominus> h)"
          using OUT_\<epsilon>k OUT_\<epsilon>h currentD_finite_OUT[OF \<epsilon>] IN_\<epsilon>k IN_\<epsilon>h currentD_finite_IN[OF \<epsilon>]
          by(auto simp add: diff_add_eq_diff_diff_swap_ennreal diff_diff_commute_ennreal)
      qed simp_all
      have g'_alt: "g' = plus_current (Sup (snd ` M)) g - h"
        by(simp add: fun_eq_iff g'_simps add_diff_eq_ennreal add.commute)

      have "current (\<Gamma> \<ominus> Sup (fst ` M)) (plus_current (Sup (snd ` M)) g)" using current g unfolding *
        by(rule SM1.current_plus_current_minus)
      hence g': "current ?\<Gamma> g'" unfolding * ** g'_alt using hM2[OF hM]
        by(rule SM1.current_minus)(auto intro!: add_increasing2 SUP_upper2 hM)

      have "wave (\<Gamma> \<ominus> Sup (fst ` M)) (plus_current (Sup (snd ` M)) g)" using current wave g g_w
        unfolding * by(rule SM1.wave_plus_current_minus)
      then have g'_w: "wave ?\<Gamma> g'" unfolding * ** g'_alt using hM2[OF hM]
        by(rule SM1.wave_minus)(auto intro!: add_increasing2 SUP_upper2 hM)

      have "hindrance_by ?\<Gamma> g' q"
      proof
        show "z \<in> A ?\<Gamma>" using z by simp
        show "z \<notin> \<E>\<^bsub>?\<Gamma>\<^esub> (TER\<^bsub>?\<Gamma>\<^esub> g')"
        proof
          assume "z \<in> \<E>\<^bsub>?\<Gamma>\<^esub> (TER\<^bsub>?\<Gamma>\<^esub> g')"
          hence OUT_z: "d_OUT g' z = 0"
            and ess: "essential ?\<Gamma> (B \<Gamma>) (TER\<^bsub>?\<Gamma>\<^esub> g') z" by(simp_all add: SINK.simps)
          from ess obtain p y where p: "path \<Gamma> z p y" and y: "y \<in> B \<Gamma>"
            and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER\<^bsub>?\<Gamma>\<^esub> g')" by(rule essentialE_RF) auto
          from y have y': "y \<notin> A \<Gamma>" using disjoint by blast
          from p z y obtain py: "p = [y]" and edge: "edge \<Gamma> z y" using disjoint
            by(cases)(auto 4 3 elim: rtrancl_path.cases dest: bipartite_E)
          hence yRF: "y \<notin> RF (TER\<^bsub>?\<Gamma>\<^esub> g')" using bypass[of y] by(auto)
          with wave_not_RF_IN_zero[OF g' g'_w, of y] have IN_g'_y: "d_IN g' y = 0"
            by(auto intro: roofed_greaterI)
          with yRF y y' have w_y: "weight ?\<Gamma> y > 0" using currentD_OUT[OF g', of y]
            by(auto simp add: RF_in_B currentD_SAT[OF g'] SINK.simps zero_less_iff_neq_zero)
          have "y \<notin> SAT (\<Gamma> \<ominus> f) g"
          proof
            assume "y \<in> SAT (\<Gamma> \<ominus> f) g"
            with y disjoint have IN_g_y: "d_IN g y = weight (\<Gamma> \<ominus> f) y" by(auto simp add: currentD_SAT[OF g])
            have "0 < weight \<Gamma> y - d_IN (\<Squnion>x\<in>M. fst x) y - d_IN h y"
              using y' w_y unfolding ** by auto
            have "d_IN g' y > 0"
              using y' w_y hM unfolding **
              apply(simp add: IN_g' IN_f IN_g_y diff_add_eq_diff_diff_swap_ennreal)
              apply(subst add_diff_eq_ennreal)
              apply(auto intro!: SUP_upper2 d_IN_mono simp: diff_add_self_ennreal diff_gt_0_iff_gt_ennreal)
              done
            with IN_g'_y show False by simp
          qed
          then have "y \<notin> TER\<^bsub>\<Gamma> \<ominus> f\<^esub> g" by simp
          with p y py have "essential \<Gamma> (B \<Gamma>) (TER\<^bsub>\<Gamma> \<ominus> f\<^esub> g) z" by(auto intro: essentialI)
          moreover with z waveD_separating[OF g_w, THEN separating_RF_A] have "z \<in> \<E>\<^bsub>?\<Omega>\<^esub> (TER\<^bsub>?\<Omega>\<^esub> g)"
            by(auto simp add: RF_in_essential)
          with z\<E> show False by contradiction
        qed
        have "\<delta> \<le> weight ?\<Gamma> z - d_OUT g' z"
          unfolding ** OUT_g' using z
          apply (simp add: \<delta>_def OUT_f diff_add_eq_diff_diff_swap_ennreal)
          apply (subst (5) diff_diff_commute_ennreal)
          apply (rule ennreal_minus_mono[OF _ order_refl])
          apply (auto simp add: ac_simps diff_add_eq_diff_diff_swap_ennreal[symmetric] add_diff_self_ennreal image_comp
                      intro!: ennreal_minus_mono[OF order_refl] SUP_upper2[OF hM] d_OUT_mono)
          done
        then show q_z: "q < weight ?\<Gamma> z - d_OUT g' z" using q_less_\<delta> by simp
        then show "d_OUT g' z < weight ?\<Gamma> z" using q_nonneg z
          by(auto simp add: less_diff_eq_ennreal less_top[symmetric] ac_simps \<Gamma>.currentD_finite_OUT[OF g']
                  intro: le_less_trans[rotated] add_increasing)
      qed
      then have hindered_by: "hindered_by (\<Gamma> \<ominus> ?\<epsilon>h \<ominus> k) q" using g' g'_w by(rule hindered_by.intros)
      then have "hindered (\<Gamma> \<ominus> ?\<epsilon>h)" using q_finite unfolding q_def by -(rule \<epsilon>h.hindered_reduce_current[OF k])
      with unhindered_h show False unfolding F_simps by contradiction
    qed
  qed

  define sat where "sat =
    (\<lambda>(\<epsilon>, h).
      let
        f = F (\<epsilon>, h);
        k = SOME k. current (\<Gamma> \<ominus> f) k \<and> wave (\<Gamma> \<ominus> f) k \<and> (\<forall>k'. current (\<Gamma> \<ominus> f) k' \<and> wave (\<Gamma> \<ominus> f) k' \<and> k \<le> k' \<longrightarrow> k = k')
      in
        if d_OUT (plus_current f k) a < weight \<Gamma> a then
          let
            \<Omega> = \<Gamma> \<ominus> f \<ominus> k;
            y = SOME y. y \<in> \<^bold>O\<^bold>U\<^bold>T\<^bsub>\<Omega>\<^esub> a \<and> weight \<Omega> y > 0;
            \<delta> = SOME \<delta>. \<delta> > 0 \<and> \<delta> < enn2real (min (weight \<Omega> a) (weight \<Omega> y)) \<and> \<not> hindered (reduce_weight \<Omega> y \<delta>)
          in
            (plus_current \<epsilon> (zero_current((a, y) := \<delta>)), plus_current h k)
        else (\<epsilon>, h))"

  have zero: "(zero_current, zero_current) \<in> Field leq"
    by(rule F_I)(simp_all add: unhindered  F_def)

  have a_TER: "a \<in> TER\<^bsub>\<Gamma> \<ominus> F \<epsilon>h\<^esub> k"
    if that: "\<epsilon>h \<in> Field leq"
    and k: "current (\<Gamma> \<ominus> F \<epsilon>h) k" and k_w: "wave (\<Gamma> \<ominus> F \<epsilon>h) k"
    and less: "d_OUT (plus_current (F \<epsilon>h) k) a < weight \<Gamma> a" for \<epsilon>h k
  proof(rule ccontr)
    assume "\<not> ?thesis"
    hence \<E>: "a \<notin> \<E>\<^bsub>\<Gamma> \<ominus> F \<epsilon>h\<^esub> (TER\<^bsub>\<Gamma> \<ominus> F \<epsilon>h\<^esub> k)" by auto
    from that have f: "current \<Gamma> (F \<epsilon>h)" and unhindered: "\<not> hindered (\<Gamma> \<ominus> F \<epsilon>h)"
       by(cases \<epsilon>h; simp add: f unhindered'; fail)+

    from less have "d_OUT k a < weight (\<Gamma> \<ominus> F \<epsilon>h) a" using a currentD_finite_OUT[OF f, of a]
      by(simp add: d_OUT_def nn_integral_add less_diff_eq_ennreal add.commute less_top[symmetric])
    with _ \<E> have "hindrance (\<Gamma> \<ominus> F \<epsilon>h) k" by(rule hindrance)(simp add: a)
    then have "hindered (\<Gamma> \<ominus> F \<epsilon>h)" using k k_w ..
    with unhindered show False by contradiction
  qed

  note minus_web_sel(2)[simp del]

  let ?P_y = "\<lambda>\<epsilon>h k y. y \<in> \<^bold>O\<^bold>U\<^bold>T\<^bsub>\<Gamma> \<ominus> F \<epsilon>h \<ominus> k\<^esub> a \<and> weight (\<Gamma> \<ominus> F \<epsilon>h \<ominus> k) y > 0"
  have Ex_y: "Ex (?P_y \<epsilon>h k)"
    if that: "\<epsilon>h \<in> Field leq"
    and k: "current (\<Gamma> \<ominus> F \<epsilon>h) k" and k_w: "wave (\<Gamma> \<ominus> F \<epsilon>h) k"
    and less: "d_OUT (plus_current (F \<epsilon>h) k) a < weight \<Gamma> a" for \<epsilon>h k
  proof(rule ccontr)
    let ?\<Omega> = "\<Gamma> \<ominus> F \<epsilon>h \<ominus> k"
    assume *: "\<not> ?thesis"

    interpret \<Gamma>: countable_bipartite_web "\<Gamma> \<ominus> F \<epsilon>h" using f[OF that] by(rule countable_bipartite_web_minus_web)
    note [simp] = weight_minus_web[OF f[OF that]] \<Gamma>.weight_minus_web[OF k]

    have "hindrance ?\<Omega> zero_current"
    proof
      show "a \<in> A ?\<Omega>" using a by simp
      show "a \<notin> \<E>\<^bsub>?\<Omega>\<^esub> (TER\<^bsub>?\<Omega>\<^esub> zero_current)" (is "a \<notin> \<E>\<^bsub>_\<^esub> ?TER")
      proof
        assume "a \<in> \<E>\<^bsub>?\<Omega>\<^esub> ?TER"
        then obtain p y where p: "path ?\<Omega> a p y" and y: "y \<in> B ?\<Omega>"
          and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF\<^bsub>?\<Omega>\<^esub> ?TER" by(rule \<E>_E_RF)(auto)
        from a p y disjoint have Nil: "p \<noteq> []" by(auto simp add: rtrancl_path_simps)
        hence "edge ?\<Omega> a (p ! 0)" "p ! 0 \<notin> RF\<^bsub>?\<Omega>\<^esub> ?TER"
          using rtrancl_path_nth[OF p, of 0] bypass by auto
        with * show False by(auto simp add: not_less outgoing_def intro: roofed_greaterI)
      qed

      have "d_OUT (plus_current (F \<epsilon>h) k) x = d_OUT (F \<epsilon>h) x + d_OUT k x" for x
        by(simp add: d_OUT_def nn_integral_add)
      then show "d_OUT zero_current a < weight ?\<Omega> a" using less a_TER[OF that k k_w less] a
        by(simp add: SINK.simps diff_gr0_ennreal)
    qed
    hence "hindered ?\<Omega>"
      by(auto intro!: hindered.intros order_trans[OF currentD_weight_OUT[OF k]] order_trans[OF currentD_weight_IN[OF k]])
    moreover have "\<not> hindered ?\<Omega>" using unhindered'[OF that] k k_w by(rule \<Gamma>.unhindered_minus_web)
    ultimately show False by contradiction
  qed

  have increasing: "\<epsilon>h \<le> sat \<epsilon>h \<and> sat \<epsilon>h \<in> Field leq" if "\<epsilon>h \<in> Field leq" for \<epsilon>h
  proof(cases \<epsilon>h)
    case (Pair \<epsilon> h)
    with that have that: "(\<epsilon>, h) \<in> Field leq" by simp
    have f: "current \<Gamma> (F (\<epsilon>, h))" and unhindered: "\<not> hindered (\<Gamma> \<ominus> F (\<epsilon>, h))"
      and \<epsilon>: "current \<Gamma> \<epsilon>"
      and h: "current (\<Gamma> \<ominus> \<epsilon>) h" and h_w: "wave (\<Gamma> \<ominus> \<epsilon>) h" and OUT_\<epsilon>: "x \<noteq> a \<Longrightarrow> d_OUT \<epsilon> x = 0" for x
      using that by(rule f unhindered' \<epsilon>_curr OUT_\<epsilon> h h_w)+
    interpret \<Gamma>: countable_bipartite_web "\<Gamma> \<ominus> F (\<epsilon>, h)" using f by(rule countable_bipartite_web_minus_web)
    note [simp] = weight_minus_web[OF f]

    let ?P_k = "\<lambda>k. current (\<Gamma> \<ominus> F (\<epsilon>, h)) k \<and> wave (\<Gamma> \<ominus> F (\<epsilon>, h)) k \<and> (\<forall>k'. current (\<Gamma> \<ominus> F (\<epsilon>, h)) k' \<and> wave (\<Gamma> \<ominus> F (\<epsilon>, h)) k' \<and> k \<le> k' \<longrightarrow> k = k')"
    define k where "k = Eps ?P_k"
    have "Ex ?P_k" by(intro ex_maximal_wave)(simp_all)
    hence "?P_k k" unfolding k_def by(rule someI_ex)
    hence k: "current (\<Gamma> \<ominus> F (\<epsilon>, h)) k" and k_w: "wave (\<Gamma> \<ominus> F (\<epsilon>, h)) k"
      and maximal: "\<And>k'. \<lbrakk> current (\<Gamma> \<ominus> F (\<epsilon>, h)) k'; wave (\<Gamma> \<ominus> F (\<epsilon>, h)) k'; k \<le> k' \<rbrakk> \<Longrightarrow> k = k'" by blast+
    note [simp] = \<Gamma>.weight_minus_web[OF k]

    let ?fk = "plus_current (F (\<epsilon>, h)) k"
    have IN_fk: "d_IN ?fk x = d_IN (F (\<epsilon>, h)) x + d_IN k x" for x
      by(simp add: d_IN_def nn_integral_add)
    have OUT_fk: "d_OUT ?fk x = d_OUT (F (\<epsilon>, h)) x + d_OUT k x" for x
      by(simp add: d_OUT_def nn_integral_add)
    have fk: "current \<Gamma> ?fk" using f k by(rule current_plus_current_minus)

    show ?thesis
    proof(cases "d_OUT ?fk a < weight \<Gamma> a")
      case less: True

      define \<Omega> where "\<Omega> = \<Gamma> \<ominus> F (\<epsilon>, h) \<ominus> k"
      have B_\<Omega> [simp]: "B \<Omega> = B \<Gamma>" by(simp add: \<Omega>_def)

      have loose: "loose \<Omega>" unfolding \<Omega>_def using unhindered k k_w maximal by(rule \<Gamma>.loose_minus_web)
      interpret \<Omega>: countable_bipartite_web \<Omega> using k unfolding \<Omega>_def
        by(rule \<Gamma>.countable_bipartite_web_minus_web)

      have a_\<E>: "a \<in> TER\<^bsub>\<Gamma> \<ominus> F (\<epsilon>, h)\<^esub> k" using that k k_w less by(rule a_TER)
      then have weight_\<Omega>_a: "weight \<Omega> a = weight \<Gamma> a - d_OUT (F (\<epsilon>, h)) a"
        using a disjoint by(auto simp add: roofed_circ_def \<Omega>_def SINK.simps)
      then have weight_a: "0 < weight \<Omega> a" using less a_\<E>
        by(simp add: OUT_fk SINK.simps diff_gr0_ennreal)

      let ?P_y = "\<lambda>y. y \<in> \<^bold>O\<^bold>U\<^bold>T\<^bsub>\<Omega>\<^esub> a \<and> weight \<Omega> y > 0"
      define y where "y = Eps ?P_y"
      have "Ex ?P_y" using that k k_w less unfolding \<Omega>_def by(rule Ex_y)
      hence "?P_y y" unfolding y_def by(rule someI_ex)
      hence y_OUT: "y \<in> \<^bold>O\<^bold>U\<^bold>T\<^bsub>\<Omega>\<^esub> a" and weight_y: "weight \<Omega> y > 0" by blast+
      from y_OUT have y_B: "y \<in> B \<Omega>" by(auto simp add: outgoing_def \<Omega>_def dest: bipartite_E)
      with weight_y have yRF: "y \<notin> RF\<^bsub>\<Gamma> \<ominus> F (\<epsilon>, h)\<^esub> (TER\<^bsub>\<Gamma> \<ominus> F (\<epsilon>, h)\<^esub> k)"
        unfolding \<Omega>_def using currentD_OUT[OF k, of y] disjoint
        by(auto split: if_split_asm simp add: SINK.simps currentD_SAT[OF k] roofed_circ_def RF_in_B \<Gamma>.currentD_finite_IN[OF k])
      hence IN_k_y: "d_IN k y = 0" by(rule wave_not_RF_IN_zero[OF k k_w])

      define bound where "bound = enn2real (min (weight \<Omega> a) (weight \<Omega> y))"
      have bound_pos: "bound > 0" using weight_y weight_a using \<Omega>.weight_finite
        by(cases "weight \<Omega> a" "weight \<Omega> y" rule: ennreal2_cases)
          (simp_all add: bound_def min_def split: if_split_asm)

      let ?P_\<delta> = "\<lambda>\<delta>. \<delta> > 0 \<and> \<delta> < bound \<and> \<not> hindered (reduce_weight \<Omega> y \<delta>)"
      define \<delta> where "\<delta> = Eps ?P_\<delta>"
      let ?\<Omega> = "reduce_weight \<Omega> y \<delta>"

      from \<Omega>.unhinder[OF loose _ weight_y bound_pos] y_B disjoint
      have "Ex ?P_\<delta>" by(auto simp add: \<Omega>_def)
      hence "?P_\<delta> \<delta>" unfolding \<delta>_def by(rule someI_ex)
      hence \<delta>_pos: "0 < \<delta>" and \<delta>_le_bound: "\<delta> < bound" and unhindered': "\<not> hindered ?\<Omega>" by blast+
      from \<delta>_pos have \<delta>_nonneg: "0 \<le> \<delta>" by simp
      from \<delta>_le_bound \<delta>_pos have \<delta>_le_a: "\<delta> < weight \<Omega> a" and \<delta>_le_y: "\<delta> < weight \<Omega> y"
        by(cases "weight \<Omega> a" "weight \<Omega> y" rule: ennreal2_cases;
           simp add: bound_def min_def ennreal_less_iff split: if_split_asm)+

      let ?\<Gamma> = "\<Gamma> \<ominus> ?fk"
      interpret \<Gamma>': countable_bipartite_web ?\<Gamma> by(rule countable_bipartite_web_minus_web fk)+
      note [simp] = weight_minus_web[OF fk]

      let ?g = "zero_current((a, y) := \<delta>)"
      have OUT_g: "d_OUT ?g x = (if x = a then \<delta> else 0)" for x
      proof(rule trans)
        show "d_OUT ?g x = (\<Sum>\<^sup>+ z. (if x = a then \<delta> else 0) * indicator {y} z)" unfolding d_OUT_def
          by(rule nn_integral_cong) simp
        show "\<dots> = (if x = a then \<delta> else 0)" using \<delta>_pos by(simp add: max_def)
      qed
      have IN_g: "d_IN ?g x = (if x = y then \<delta> else 0)" for x
      proof(rule trans)
        show "d_IN ?g x = (\<Sum>\<^sup>+ z. (if x = y then \<delta> else 0) * indicator {a} z)" unfolding d_IN_def
          by(rule nn_integral_cong) simp
        show "\<dots> = (if x = y then \<delta> else 0)" using \<delta>_pos by(simp add: max_def)
      qed

      have g: "current ?\<Gamma> ?g"
      proof
        show "d_OUT ?g x \<le> weight ?\<Gamma> x" for x
        proof(cases "x = a")
          case False
          then show ?thesis using currentD_weight_OUT[OF fk, of x] currentD_weight_IN[OF fk, of x]
            by(auto simp add: OUT_g zero_ennreal_def[symmetric])
        next
          case True
          then show ?thesis using \<delta>_le_a a a_\<E> \<delta>_pos unfolding OUT_g
            by(simp add: OUT_g \<Omega>_def SINK.simps OUT_fk split: if_split_asm)
        qed
        show "d_IN ?g x \<le> weight ?\<Gamma> x" for x
        proof(cases "x = y")
          case False
          then show ?thesis using currentD_weight_OUT[OF fk, of x] currentD_weight_IN[OF fk, of x]
            by(auto simp add: IN_g zero_ennreal_def[symmetric])
        next
          case True
          then show ?thesis using \<delta>_le_y y_B a_\<E> \<delta>_pos currentD_OUT[OF k, of y] IN_k_y
            by(simp add: OUT_g \<Omega>_def SINK.simps OUT_fk IN_fk IN_g split: if_split_asm)
        qed
        show "?g e = 0" if "e \<notin> \<^bold>E\<^bsub>?\<Gamma>\<^esub>" for e using y_OUT that by(auto simp add: \<Omega>_def outgoing_def)
      qed
      interpret \<Gamma>'': web "\<Gamma> \<ominus> ?fk \<ominus> ?g" using g by(rule \<Gamma>'.web_minus_web)

      let ?\<epsilon>' = "plus_current \<epsilon> (zero_current((a, y) := \<delta>))"
      let ?h' = "plus_current h k"
      have F': "F (?\<epsilon>', ?h') = plus_current (plus_current (F (\<epsilon>, h)) k) (zero_current((a, y) := \<delta>))" (is "_ = ?f'")
        by(auto simp add: F_simps fun_eq_iff add_ac)
      have sat: "sat (\<epsilon>, h) = (?\<epsilon>', ?h')" using less
        by(simp add: sat_def k_def \<Omega>_def Let_def y_def bound_def \<delta>_def)

      have le: "(\<epsilon>, h) \<le> (?\<epsilon>', ?h')" using \<delta>_pos
        by(auto simp add: le_fun_def add_increasing2 add_increasing)

      have "current (\<Gamma> \<ominus> \<epsilon>) ((\<lambda>_. 0)((a, y) := ennreal \<delta>))" using g
        by(rule current_weight_mono)(auto simp add: weight_minus_web[OF \<epsilon>] intro!: ennreal_minus_mono d_OUT_mono d_IN_mono, simp_all add: F_def add_increasing2)
      with \<epsilon> have \<epsilon>': "current \<Gamma> ?\<epsilon>'" by(rule current_plus_current_minus)
      moreover have eq_0: "d_OUT ?\<epsilon>' x = 0" if "x \<noteq> a" for x unfolding plus_current_def using that
        by(subst d_OUT_add)(simp_all add: \<delta>_nonneg d_OUT_fun_upd OUT_\<epsilon>)
      moreover
      from \<epsilon>' interpret \<epsilon>': countable_bipartite_web "\<Gamma> \<ominus> ?\<epsilon>'" by(rule countable_bipartite_web_minus_web)
      from \<epsilon> interpret \<epsilon>: countable_bipartite_web "\<Gamma> \<ominus> \<epsilon>" by(rule countable_bipartite_web_minus_web)
      have g': "current (\<Gamma> \<ominus> \<epsilon>) ?g" using g
        apply(rule current_weight_mono)
        apply(auto simp add: weight_minus_web[OF \<epsilon>] intro!: ennreal_minus_mono d_OUT_mono d_IN_mono)
        apply(simp_all add: F_def add_increasing2)
        done
      have k': "current (\<Gamma> \<ominus> \<epsilon> \<ominus> h) k" using k unfolding F_simps minus_plus_current[OF \<epsilon> h] .
      with h have "current (\<Gamma> \<ominus> \<epsilon>) (plus_current h k)" by(rule \<epsilon>.current_plus_current_minus)
      hence "current (\<Gamma> \<ominus> \<epsilon>) (plus_current (plus_current h k) ?g)" using g unfolding minus_plus_current[OF f k]
        unfolding F_simps minus_plus_current[OF \<epsilon> h] \<epsilon>.minus_plus_current[OF h k', symmetric]
        by(rule \<epsilon>.current_plus_current_minus)
      then have "current (\<Gamma> \<ominus> \<epsilon> \<ominus> ?g) (plus_current (plus_current h k) ?g - ?g)" using g'
        by(rule \<epsilon>.current_minus)(auto simp add: add_increasing)
      then have h'': "current (\<Gamma> \<ominus> ?\<epsilon>') ?h'"
        by(rule arg_cong2[where f=current, THEN iffD1, rotated -1])
          (simp_all add: minus_plus_current[OF \<epsilon> g'] fun_eq_iff add_diff_eq_ennreal[symmetric])
      moreover have "wave (\<Gamma> \<ominus> ?\<epsilon>') ?h'"
      proof
        have "separating (\<Gamma> \<ominus> \<epsilon>) (TER\<^bsub>\<Gamma> \<ominus> \<epsilon>\<^esub> (plus_current h k))"
          using k k_w unfolding F_simps minus_plus_current[OF \<epsilon> h]
          by(intro waveD_separating \<epsilon>.wave_plus_current_minus[OF h h_w])
        moreover have "TER\<^bsub>\<Gamma> \<ominus> \<epsilon>\<^esub> (plus_current h k) \<subseteq> TER\<^bsub>\<Gamma> \<ominus> ?\<epsilon>'\<^esub> (plus_current h k)"
          by(auto 4 4 simp add: SAT.simps weight_minus_web[OF \<epsilon>] weight_minus_web[OF \<epsilon>'] split: if_split_asm elim: order_trans[rotated] intro!: ennreal_minus_mono d_IN_mono add_increasing2 \<delta>_nonneg)
        ultimately show sep: "separating (\<Gamma> \<ominus> ?\<epsilon>') (TER\<^bsub>\<Gamma> \<ominus> ?\<epsilon>'\<^esub> ?h')"
          by(simp add: minus_plus_current[OF \<epsilon> g'] separating_weakening)
      qed(rule h'')
      moreover
      have "\<not> hindered (\<Gamma> \<ominus> F (?\<epsilon>', ?h'))" using unhindered'
      proof(rule contrapos_nn)
        assume "hindered (\<Gamma> \<ominus> F (?\<epsilon>', ?h'))"
        thus "hindered ?\<Omega>"
        proof(rule hindered_mono_web[rotated -1])
          show "weight ?\<Omega> z = weight (\<Gamma> \<ominus> F (?\<epsilon>', ?h')) z" if "z \<notin> A (\<Gamma> \<ominus> F (?\<epsilon>', ?h'))" for z
            using that unfolding F'
            apply(cases "z = y")
            apply(simp_all add: \<Omega>_def minus_plus_current[OF fk g] \<Gamma>'.weight_minus_web[OF g] IN_g)
            apply(simp_all add: plus_current_def d_IN_add diff_add_eq_diff_diff_swap_ennreal currentD_finite_IN[OF f])
            done
          have "y \<noteq> a" using y_B a disjoint by auto
          then show "weight (\<Gamma> \<ominus> F (?\<epsilon>', ?h')) z \<le> weight ?\<Omega> z" if "z \<in> A (\<Gamma> \<ominus> F (?\<epsilon>', ?h'))" for z
            using that y_B disjoint \<delta>_nonneg unfolding F'
            apply(cases "z = a")
            apply(simp_all add: \<Omega>_def minus_plus_current[OF fk g] \<Gamma>'.weight_minus_web[OF g] OUT_g)
            apply(auto simp add: plus_current_def d_OUT_add diff_add_eq_diff_diff_swap_ennreal currentD_finite_OUT[OF f])
            done
        qed(simp_all add: \<Omega>_def)
      qed
      ultimately have "(?\<epsilon>', ?h') \<in> Field leq" by-(rule F_I)
      with Pair le sat that show ?thesis by(auto)
    next
      case False
      with currentD_weight_OUT[OF fk, of a] have "d_OUT ?fk a = weight \<Gamma> a" by simp
      have "sat \<epsilon>h = \<epsilon>h" using False Pair by(simp add: sat_def k_def)
      thus ?thesis using that Pair by(auto)
    qed
  qed

  have "bourbaki_witt_fixpoint Sup leq sat" using increasing chain_Field unfolding leq_def
    by(intro bourbaki_witt_fixpoint_restrict_rel)(auto intro: Sup_upper Sup_least)
  then interpret bourbaki_witt_fixpoint Sup leq sat .

  define f where "f = fixp_above (zero_current, zero_current)"
  have Field: "f \<in> Field leq" using fixp_above_Field[OF zero] unfolding f_def .
  then have f: "current \<Gamma> (F f)" and unhindered: "\<not> hindered (\<Gamma> \<ominus> F f)"
    by(cases f; simp add: f unhindered'; fail)+
  interpret \<Gamma>: countable_bipartite_web "\<Gamma> \<ominus> F f" using f by(rule countable_bipartite_web_minus_web)
  note [simp] = weight_minus_web[OF f]
  have Field': "(fst f, snd f) \<in> Field leq" using Field by simp

  let ?P_k = "\<lambda>k. current (\<Gamma> \<ominus> F f) k \<and> wave (\<Gamma> \<ominus> F f) k \<and> (\<forall>k'. current (\<Gamma> \<ominus> F f) k' \<and> wave (\<Gamma> \<ominus> F f) k' \<and> k \<le> k' \<longrightarrow> k = k')"
  define k where "k = Eps ?P_k"
  have "Ex ?P_k" by(intro ex_maximal_wave)(simp_all)
  hence "?P_k k" unfolding k_def by(rule someI_ex)
  hence k: "current (\<Gamma> \<ominus> F f) k" and k_w: "wave (\<Gamma> \<ominus> F f) k"
    and maximal: "\<And>k'. \<lbrakk> current (\<Gamma> \<ominus> F f) k'; wave (\<Gamma> \<ominus> F f) k'; k \<le> k' \<rbrakk> \<Longrightarrow> k = k'" by blast+
  note [simp] = \<Gamma>.weight_minus_web[OF k]

  let ?fk = "plus_current (F f) k"
  have IN_fk: "d_IN ?fk x = d_IN (F f) x + d_IN k x" for x
    by(simp add: d_IN_def nn_integral_add)
  have OUT_fk: "d_OUT ?fk x = d_OUT (F f) x + d_OUT k x" for x
    by(simp add: d_OUT_def nn_integral_add)
  have fk: "current \<Gamma> ?fk" using f k by(rule current_plus_current_minus)

  have "d_OUT ?fk a \<ge> weight \<Gamma> a"
  proof(rule ccontr)
    assume "\<not> ?thesis"
    hence less: "d_OUT ?fk a < weight \<Gamma> a" by simp

    define \<Omega> where "\<Omega> = \<Gamma> \<ominus> F f \<ominus> k"
    have B_\<Omega> [simp]: "B \<Omega> = B \<Gamma>" by(simp add: \<Omega>_def)

    have loose: "loose \<Omega>" unfolding \<Omega>_def using unhindered k k_w maximal by(rule \<Gamma>.loose_minus_web)
    interpret \<Omega>: countable_bipartite_web \<Omega> using k unfolding \<Omega>_def
      by(rule \<Gamma>.countable_bipartite_web_minus_web)

    have a_\<E>: "a \<in> TER\<^bsub>\<Gamma> \<ominus> F f\<^esub> k" using Field k k_w less by(rule a_TER)
    then have "weight \<Omega> a = weight \<Gamma> a - d_OUT (F f) a"
      using a disjoint by(auto simp add: roofed_circ_def \<Omega>_def SINK.simps)
    then have weight_a: "0 < weight \<Omega> a" using less a_\<E>
      by(simp add: OUT_fk SINK.simps diff_gr0_ennreal)

    let ?P_y = "\<lambda>y. y \<in> \<^bold>O\<^bold>U\<^bold>T\<^bsub>\<Omega>\<^esub> a \<and> weight \<Omega> y > 0"
    define y where "y = Eps ?P_y"
    have "Ex ?P_y" using Field k k_w less unfolding \<Omega>_def by(rule Ex_y)
    hence "?P_y y" unfolding y_def by(rule someI_ex)
    hence "y \<in> \<^bold>O\<^bold>U\<^bold>T\<^bsub>\<Omega>\<^esub> a" and weight_y: "weight \<Omega> y > 0" by blast+
    then have y_B: "y \<in> B \<Omega>" by(auto simp add: outgoing_def \<Omega>_def dest: bipartite_E)

    define bound where "bound = enn2real (min (weight \<Omega> a) (weight \<Omega> y))"
    have bound_pos: "bound > 0" using weight_y weight_a \<Omega>.weight_finite
      by(cases "weight \<Omega> a" "weight \<Omega> y" rule: ennreal2_cases)
        (simp_all add: bound_def min_def split: if_split_asm)

    let ?P_\<delta> = "\<lambda>\<delta>. \<delta> > 0 \<and> \<delta> < bound \<and> \<not> hindered (reduce_weight \<Omega> y \<delta>)"
    define \<delta> where "\<delta> = Eps ?P_\<delta>"
    from \<Omega>.unhinder[OF loose _ weight_y bound_pos] y_B disjoint have "Ex ?P_\<delta>" by(auto simp add: \<Omega>_def)
    hence "?P_\<delta> \<delta>" unfolding \<delta>_def by(rule someI_ex)
    hence \<delta>_pos: "0 < \<delta>" by blast+

    let ?f' = "(plus_current (fst f) (zero_current((a, y) := \<delta>)), plus_current (snd f) k)"
    have sat: "?f' = sat f" using less by(simp add: sat_def k_def \<Omega>_def Let_def y_def bound_def \<delta>_def split_def)
    also have "\<dots> = f" unfolding f_def using fixp_above_unfold[OF zero] by simp
    finally have "fst ?f' (a, y) = fst f (a, y)" by simp
    hence "\<delta> = 0" using currentD_finite[OF \<epsilon>_curr[OF Field']] \<delta>_pos
      by(cases "fst f (a, y)") simp_all
    with \<delta>_pos show False by simp
  qed

  with currentD_weight_OUT[OF fk, of a] have "d_OUT ?fk a = weight \<Gamma> a" by simp
  moreover have "current \<Gamma> ?fk" using f k by(rule current_plus_current_minus)
  moreover have "\<not> hindered (\<Gamma> \<ominus> ?fk)" unfolding minus_plus_current[OF f k]
    using unhindered k k_w by(rule \<Gamma>.unhindered_minus_web)
  ultimately show ?thesis by blast
qed

end

subsection \<open>Linkability of unhindered bipartite webs\<close>

context countable_bipartite_web begin

theorem unhindered_linkable:
  assumes unhindered: "\<not> hindered \<Gamma>"
  shows "linkable \<Gamma>"
proof(cases "A \<Gamma> = {}")
  case True
  thus ?thesis by(auto intro!: exI[where x="zero_current"] linkage.intros simp add: web_flow_iff )
next
  case nempty: False

  let ?P = "\<lambda>f a f'. current (\<Gamma> \<ominus> f) f' \<and> d_OUT f' a = weight (\<Gamma> \<ominus> f) a \<and> \<not> hindered (\<Gamma> \<ominus> f \<ominus> f')"

  define enum where "enum = from_nat_into (A \<Gamma>)"
  have enum_A: "enum n \<in> A \<Gamma>" for n using from_nat_into[OF nempty, of n] by(simp add: enum_def)
  have vertex_enum [simp]: "vertex \<Gamma> (enum n)" for n using enum_A[of n] A_vertex by blast

  define f where "f = rec_nat zero_current (\<lambda>n f. let f' = SOME f'. ?P f (enum n) f' in plus_current f f')"
  have f_0 [simp]: "f 0 = zero_current" by(simp add: f_def)
  have f_Suc: "f (Suc n) = plus_current (f n) (Eps (?P (f n) (enum n)))" for n by(simp add: f_def)

  have f: "current \<Gamma> (f n)"
    and sat: "\<And>m. m < n \<Longrightarrow> d_OUT (f n) (enum m) = weight \<Gamma> (enum m)"
    and unhindered: "\<not> hindered (\<Gamma> \<ominus> f n)" for n
  proof(induction n)
    case 0
    { case 1 thus ?case by(simp add: ) }
    { case 2 thus ?case by simp }
    { case 3 thus ?case using unhindered by simp }
  next
    case (Suc n)
    interpret \<Gamma>: countable_bipartite_web "\<Gamma> \<ominus> f n" using Suc.IH(1) by(rule countable_bipartite_web_minus_web)

    define f' where "f' = Eps (?P (f n) (enum n))"
    have "Ex (?P (f n) (enum n))" using Suc.IH(3) by(rule \<Gamma>.unhindered_saturate1)(simp add: enum_A)
    hence "?P (f n) (enum n) f'" unfolding f'_def by(rule someI_ex)
    hence f': "current (\<Gamma> \<ominus> f n) f'"
      and OUT: "d_OUT f' (enum n) = weight (\<Gamma> \<ominus> f n) (enum n)"
      and unhindered': "\<not> hindered (\<Gamma> \<ominus> f n \<ominus> f')" by blast+
    have f_Suc: "f (Suc n) = plus_current (f n) f'" by(simp add: f'_def f_Suc)
    { case 1 show ?case unfolding f_Suc using Suc.IH(1) f' by(rule current_plus_current_minus) }
    note f'' = this
    { case (2 m)
      have "d_OUT (f (Suc n)) (enum m) \<le> weight \<Gamma> (enum m)" using f'' by(rule currentD_weight_OUT)
      moreover have "weight \<Gamma> (enum m) \<le> d_OUT (f (Suc n)) (enum m)"
      proof(cases "m = n")
        case True
        then show ?thesis unfolding f_Suc using OUT True
          by(simp add: d_OUT_def nn_integral_add enum_A add_diff_self_ennreal less_imp_le)
      next
        case False
        hence "m < n" using 2 by simp
        thus ?thesis using Suc.IH(2)[OF \<open>m < n\<close>] unfolding f_Suc
          by(simp add: d_OUT_def nn_integral_add add_increasing2 )
      qed
      ultimately show ?case by(rule antisym) }
    { case 3 show ?case unfolding f_Suc minus_plus_current[OF Suc.IH(1) f'] by(rule unhindered') }
  qed
  interpret \<Gamma>: countable_bipartite_web "\<Gamma> \<ominus> f n" for n using f by(rule countable_bipartite_web_minus_web)

  have Ex_P: "Ex (?P (f n) (enum n))" for n using unhindered by(rule \<Gamma>.unhindered_saturate1)(simp add: enum_A)
  have f_mono: "f n \<le> f (Suc n)" for n using someI_ex[OF Ex_P, of n]
    by(auto simp add: le_fun_def f_Suc enum_A intro: add_increasing2 dest: )
  hence incseq: "incseq f" by(rule incseq_SucI)
  hence chain: "Complete_Partial_Order.chain (\<le>) (range f)" by(rule incseq_chain_range)

  define g where "g = Sup (range f)"
  have "support_flow g \<subseteq> \<^bold>E"
    by (auto simp add: g_def support_flow.simps currentD_outside [OF f] image_comp elim: contrapos_pp)
  then have countable_g: "countable (support_flow g)" by(rule countable_subset) simp
  with chain _ _ have g: "current \<Gamma> g" unfolding g_def  by(rule current_Sup)(auto simp add: f)
  moreover
  have "d_OUT g x = weight \<Gamma> x" if "x \<in> A \<Gamma>" for x
  proof(rule antisym)
    show "d_OUT g x \<le> weight \<Gamma> x" using g by(rule currentD_weight_OUT)
    have "countable (A \<Gamma>)" using A_vertex by(rule countable_subset) simp
    from that subset_range_from_nat_into[OF this] obtain n where "x = enum n" unfolding enum_def by blast
    with sat[of n "Suc n"] have "d_OUT (f (Suc n)) x \<ge> weight \<Gamma> x" by simp
    then show "weight \<Gamma> x \<le> d_OUT g x" using countable_g unfolding g_def
      by(subst d_OUT_Sup[OF chain])(auto intro: SUP_upper2)
  qed
  ultimately show ?thesis by(auto simp add: web_flow_iff linkage.simps)
qed

end


context countable_web begin

theorem loose_linkable: \<comment> \<open>Theorem 6.2\<close>
  assumes "loose \<Gamma>"
  shows "linkable \<Gamma>"
proof -
  interpret bi: countable_bipartite_web "bipartite_web_of \<Gamma>" by(rule countable_bipartite_web_of)
  have "\<not> hindered (bipartite_web_of \<Gamma>)" using assms by(rule unhindered_bipartite_web_of)
  then have "linkable (bipartite_web_of \<Gamma>)"
    by(rule bi.unhindered_linkable)
  then show ?thesis by(rule linkable_bipartite_web_ofD) simp
qed

lemma ex_orthogonal_current: \<comment> \<open>Lemma 4.15\<close>
  "\<exists>f S. web_flow \<Gamma> f \<and> separating \<Gamma> S \<and> orthogonal_current \<Gamma> f S"
  by(rule ex_orthogonal_current')(rule countable_web.loose_linkable[OF countable_web_quotient_web])

end

subsection \<open>Glueing the reductions together\<close>

context countable_network begin

context begin

qualified lemma max_flow_min_cut':
  assumes source_in: "\<And>x. \<not> edge \<Delta> x (source \<Delta>)"
  and sink_out: "\<And>y. \<not> edge \<Delta> (sink \<Delta>) y"
  and undead: "\<And>x y. edge \<Delta> x y \<Longrightarrow> (\<exists>z. edge \<Delta> y z) \<or> (\<exists>z. edge \<Delta> z x)"
  and source_sink: "\<not> edge \<Delta> (source \<Delta>) (sink \<Delta>)"
  and no_loop: "\<And>x. \<not> edge \<Delta> x x"
  and capacity_pos: "\<And>e. e \<in> \<^bold>E \<Longrightarrow> capacity \<Delta> e > 0"
  shows "\<exists>f S. flow \<Delta> f \<and> cut \<Delta> S \<and> orthogonal \<Delta> f S"
  by(rule max_flow_min_cut')(rule countable_web.ex_orthogonal_current[OF countable_web_web_of_network], fact+)

qualified lemma max_flow_min_cut'':
  assumes sink_out: "\<And>y. \<not> edge \<Delta> (sink \<Delta>) y"
  and source_in: "\<And>x. \<not> edge \<Delta> x (source \<Delta>)"
  and no_loop: "\<And>x. \<not> edge \<Delta> x x"
  and capacity_pos: "\<And>e. e \<in> \<^bold>E \<Longrightarrow> capacity \<Delta> e > 0"
  shows "\<exists>f S. flow \<Delta> f \<and> cut \<Delta> S \<and> orthogonal \<Delta> f S"
proof -
  interpret antiparallel_edges \<Delta> ..
  interpret \<Delta>'': countable_network \<Delta>'' by(rule \<Delta>''_countable_network)
  have "\<exists>f S. flow \<Delta>'' f \<and> cut \<Delta>'' S \<and> orthogonal \<Delta>'' f S"
    by(rule \<Delta>''.max_flow_min_cut')(auto simp add: sink_out source_in no_loop capacity_pos elim: edg.cases)
  then obtain f S where f: "flow \<Delta>'' f" and cut: "cut \<Delta>'' S" and ortho: "orthogonal \<Delta>'' f S" by blast
  have "flow \<Delta> (collect f)" using f by(rule flow_collect)
  moreover have "cut \<Delta> (cut' S)" using cut by(rule cut_cut')
  moreover have "orthogonal \<Delta> (collect f) (cut' S)" using ortho f by(rule orthogonal_cut')
  ultimately show ?thesis by blast
qed

qualified lemma max_flow_min_cut''':
  assumes sink_out: "\<And>y. \<not> edge \<Delta> (sink \<Delta>) y"
  and source_in: "\<And>x. \<not> edge \<Delta> x (source \<Delta>)"
  and capacity_pos: "\<And>e. e \<in> \<^bold>E \<Longrightarrow> capacity \<Delta> e > 0"
  shows "\<exists>f S. flow \<Delta> f \<and> cut \<Delta> S \<and> orthogonal \<Delta> f S"
proof -
  interpret antiparallel_edges \<Delta> ..
  interpret \<Delta>'': countable_network \<Delta>'' by(rule \<Delta>''_countable_network)
  have "\<exists>f S. flow \<Delta>'' f \<and> cut \<Delta>'' S \<and> orthogonal \<Delta>'' f S"
    by(rule \<Delta>''.max_flow_min_cut'')(auto simp add: sink_out source_in capacity_pos elim: edg.cases)
  then obtain f S where f: "flow \<Delta>'' f" and cut: "cut \<Delta>'' S" and ortho: "orthogonal \<Delta>'' f S" by blast
  have "flow \<Delta> (collect f)" using f by(rule flow_collect)
  moreover have "cut \<Delta> (cut' S)" using cut by(rule cut_cut')
  moreover have "orthogonal \<Delta> (collect f) (cut' S)" using ortho f by(rule orthogonal_cut')
  ultimately show ?thesis by blast
qed

theorem max_flow_min_cut:
  "\<exists>f S. flow \<Delta> f \<and> cut \<Delta> S \<and> orthogonal \<Delta> f S"
proof -
  interpret \<Delta>''': countable_network \<Delta>''' by(rule \<Delta>'''_countable_network)
  have "\<exists>f S. flow \<Delta>''' f \<and> cut \<Delta>''' S \<and> orthogonal \<Delta>''' f S" by(rule \<Delta>'''.max_flow_min_cut''') auto
  then obtain f S where f: "flow \<Delta>''' f" and cut: "cut \<Delta>''' S" and ortho: "orthogonal \<Delta>''' f S" by blast
  from flow_\<Delta>'''[OF this] show ?thesis by blast
qed

end

end

end
