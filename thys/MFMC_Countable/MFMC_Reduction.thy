section \<open>Reductions\<close>

theory MFMC_Reduction imports 
  MFMC_Web
begin

subsection \<open>From a web to a bipartite web\<close>

definition bipartite_web_of :: "('v, 'more) web_scheme \<Rightarrow> ('v + 'v, 'more) web_scheme"
where
  "bipartite_web_of \<Gamma> =
  \<lparr>edge = \<lambda>uv uv'. case (uv, uv') of (Inl u, Inr v) \<Rightarrow> edge \<Gamma> u v \<or> u = v \<and> u \<in> vertices \<Gamma> \<and> u \<notin> A \<Gamma> \<and> v \<notin> B \<Gamma> | _ \<Rightarrow> False,
   weight = \<lambda>uv. case uv of Inl u \<Rightarrow> if u \<in> B \<Gamma> then 0 else weight \<Gamma> u | Inr u \<Rightarrow> if u \<in> A \<Gamma> then 0 else weight \<Gamma> u,
   A = Inl ` (vertices \<Gamma> - B \<Gamma>),
   B = Inr ` (- A \<Gamma>),
   \<dots> = web.more \<Gamma>\<rparr>"

lemma bipartite_web_of_sel [simp]: fixes \<Gamma> (structure) shows
  "edge (bipartite_web_of \<Gamma>) (Inl u) (Inr v) \<longleftrightarrow> edge \<Gamma> u v \<or> u = v \<and> u \<in> \<^bold>V \<and> u \<notin> A \<Gamma> \<and> v \<notin> B \<Gamma>"
  "edge (bipartite_web_of \<Gamma>) uv (Inl u) \<longleftrightarrow> False"
  "edge (bipartite_web_of \<Gamma>) (Inr v) uv \<longleftrightarrow> False"
  "weight (bipartite_web_of \<Gamma>) (Inl u) = (if u \<in> B \<Gamma> then 0 else weight \<Gamma> u)"
  "weight (bipartite_web_of \<Gamma>) (Inr v) = (if v \<in> A \<Gamma> then 0 else weight \<Gamma> v)"
  "A (bipartite_web_of \<Gamma>) = Inl ` (\<^bold>V - B \<Gamma>)"
  "B (bipartite_web_of \<Gamma>) = Inr ` (- A \<Gamma>)"
by(simp_all add: bipartite_web_of_def split: sum.split)

lemma edge_bipartite_webI1: "edge \<Gamma> u v \<Longrightarrow> edge (bipartite_web_of \<Gamma>) (Inl u) (Inr v)"
by(auto)

lemma edge_bipartite_webI2:
  "\<lbrakk> u \<in> \<^bold>V\<^bsub>\<Gamma>\<^esub>; u \<notin> A \<Gamma>; u \<notin> B \<Gamma> \<rbrakk> \<Longrightarrow> edge (bipartite_web_of \<Gamma>) (Inl u) (Inr u)"
by(auto)

lemma edge_bipartite_webE:
  fixes \<Gamma> (structure)
  assumes "edge (bipartite_web_of \<Gamma>) uv uv'"
  obtains u v where "uv = Inl u" "uv' = Inr v" "edge \<Gamma> u v"
    | u where "uv = Inl u" "uv' = Inr u" "u \<in> \<^bold>V" "u \<notin> A \<Gamma>" "u \<notin> B \<Gamma>"
using assms by(cases uv uv' rule: sum.exhaust[case_product sum.exhaust]) auto

lemma E_bipartite_web:
  fixes \<Gamma> (structure) shows
  "\<^bold>E\<^bsub>bipartite_web_of \<Gamma>\<^esub> = (\<lambda>(x, y). (Inl x, Inr y)) ` \<^bold>E \<union> (\<lambda>x. (Inl x, Inr x)) ` (\<^bold>V - A \<Gamma> - B \<Gamma>)"
by(auto elim: edge_bipartite_webE)

context web begin

lemma vertex_bipartite_web [simp]:
  "vertex (bipartite_web_of \<Gamma>) (Inl x) \<longleftrightarrow> vertex \<Gamma> x \<and> x \<notin> B \<Gamma>"
  "vertex (bipartite_web_of \<Gamma>) (Inr x) \<longleftrightarrow> vertex \<Gamma> x \<and> x \<notin> A \<Gamma>"
by(auto 4 4 simp add: vertex_def dest: B_out A_in intro: edge_bipartite_webI1 edge_bipartite_webI2 elim!: edge_bipartite_webE)

definition separating_of_bipartite :: "('v + 'v) set \<Rightarrow> 'v set"
where
  "separating_of_bipartite S =
  (let A_S = Inl -` S; B_S = Inr -` S in (A_S \<inter> B_S) \<union> (A \<Gamma> \<inter> A_S) \<union> (B \<Gamma> \<inter> B_S))"

context
  fixes S :: "('v + 'v) set"
  assumes sep: "separating (bipartite_web_of \<Gamma>) S"
begin

text \<open>Proof of separation follows @{cite Aharoni1983EJC}\<close>

lemma separating_of_bipartite_aux:
  assumes p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
  and x: "x \<in> A \<Gamma> \<or> Inr x \<in> S"
  shows "(\<exists>z\<in>set p. z \<in> separating_of_bipartite S) \<or> x \<in> separating_of_bipartite S"
proof(cases "p = []")
  case True
  with p have "x = y" by cases auto
  with y x have "x \<in> separating_of_bipartite S" using disjoint
    by(auto simp add: separating_of_bipartite_def Let_def)
  thus ?thesis ..
next
  case nNil: False
  define inmarked where "inmarked x \<longleftrightarrow> x \<in> A \<Gamma> \<or> Inr x \<in> S" for x
  define outmarked where "outmarked x \<longleftrightarrow> x \<in> B \<Gamma> \<or> Inl x \<in> S" for x
  let ?\<Gamma> = "bipartite_web_of \<Gamma>"
  let ?double = "\<lambda>x. inmarked x \<and> outmarked x"
  define tailmarked where "tailmarked = (\<lambda>(x, y :: 'v). outmarked x)"
  define headmarked where "headmarked = (\<lambda>(x :: 'v, y). inmarked y)"

  have marked_E: "tailmarked e \<or> headmarked e" if "e \<in> \<^bold>E" for e \<comment> \<open>Lemma 1b\<close>
  proof(cases e)
    case (Pair x y)
    with that have "path ?\<Gamma> (Inl x) [Inr y] (Inr y)" by(auto intro!: rtrancl_path.intros)
    from separatingD[OF sep this] that Pair show ?thesis
      by(fastforce simp add: vertex_def inmarked_def outmarked_def tailmarked_def headmarked_def)
  qed

  have "\<exists>z\<in>set (x # p). ?double z" \<comment> \<open>Lemma 2\<close>
  proof -
    have "inmarked ((x # p) ! (i + 1)) \<or> outmarked ((x # p) ! i)" if "i < length p" for i
      using rtrancl_path_nth[OF p that] marked_E[of "((x # p) ! i, p ! i)"] that
      by(auto simp add: tailmarked_def headmarked_def nth_Cons split: nat.split)
    hence "{i. i < length p \<and> inmarked (p ! i)} \<union> {i. i < length (x # butlast p) \<and> outmarked ((x # butlast p) ! i)} = {i. i < length p}"
      (is "?in \<union> ?out = _") using nNil
      by(force simp add: nth_Cons' nth_butlast elim: meta_allE[where x=0] cong del: old.nat.case_cong_weak)
    hence "length p + 2 = card (?in \<union> ?out) + 2" by simp
    also have "\<dots> \<le> (card ?in + 1) + (card ?out + 1)" by(simp add: card_Un_le)
    also have "card ?in = card ((\<lambda>i. Inl (i + 1) :: _ + nat) ` ?in)"
      by(rule card_image[symmetric])(simp add: inj_on_def)
    also have "\<dots> + 1 = card (insert (Inl 0) {Inl (Suc i) :: _ + nat|i. i < length p \<and> inmarked (p ! i)})"
      by(subst card_insert_if)(auto intro!: arg_cong[where f=card])
    also have "\<dots> = card {Inl i :: nat + nat|i. i < length (x # p) \<and> inmarked ((x # p) ! i)}" (is "_ = card ?in")
      using x by(intro arg_cong[where f=card])(auto simp add: nth_Cons inmarked_def split: nat.split_asm)
    also have "card ?out = card ((Inr :: _ \<Rightarrow> nat + _) ` ?out)" by(simp add: card_image)
    also have "\<dots> + 1 = card (insert (Inr (length p)) {Inr i :: nat + _|i. i < length p \<and> outmarked ((x # p) ! i)})"
      using nNil by(subst card_insert_if)(auto intro!: arg_cong[where f=card] simp add: nth_Cons nth_butlast cong: nat.case_cong)
    also have "\<dots> = card {Inr i :: nat + _|i. i < length (x # p) \<and> outmarked ((x # p) ! i)}" (is "_ = card ?out")
      using nNil rtrancl_path_last[OF p nNil] y
      by(intro arg_cong[where f=card])(auto simp add: outmarked_def last_conv_nth)
    also have "card ?in + card ?out = card (?in \<union> ?out)"
      by(rule card_Un_disjoint[symmetric]) auto
    also let ?f = "case_sum id id"
    have "?f ` (?in \<union> ?out) \<subseteq> {i. i < length (x # p)}" by auto
    from card_mono[OF _ this] have "card (?f ` (?in \<union> ?out)) \<le> length p + 1" by simp
    ultimately have "\<not> inj_on ?f (?in \<union> ?out)" by(intro pigeonhole) simp
    then obtain i where "i < length (x # p)" "?double ((x # p) ! i)"
      by(auto simp add: inj_on_def)
    thus ?thesis by(auto simp add: set_conv_nth)
  qed
  moreover have "z \<in> separating_of_bipartite S" if "?double z" for z using that disjoint
    by(auto simp add: separating_of_bipartite_def Let_def inmarked_def outmarked_def)
  ultimately show ?thesis by auto
qed

lemma separating_of_bipartite:
  "separating \<Gamma> (separating_of_bipartite S)"
by(rule separating_gen.intros)(erule (1) separating_of_bipartite_aux; simp)

end

lemma current_bipartite_web_finite:
  assumes f: "current (bipartite_web_of \<Gamma>) f" (is "current ?\<Gamma> _")
  shows "f e \<noteq> \<top>"
proof(cases e)
  case (Pair x y)
  have "f e \<le> d_OUT f x" unfolding Pair d_OUT_def by(rule nn_integral_ge_point) simp
  also have "\<dots> \<le> weight ?\<Gamma> x" by(rule currentD_weight_OUT[OF f])
  also have "\<dots> < \<top>" by(cases x)(simp_all add: less_top[symmetric])
  finally show ?thesis by simp
qed

definition current_of_bipartite :: "('v + 'v) current \<Rightarrow> 'v current"
where "current_of_bipartite f = (\<lambda>(x, y). f (Inl x, Inr y) * indicator \<^bold>E (x, y))"

lemma current_of_bipartite_simps [simp]: "current_of_bipartite f (x, y) = f (Inl x, Inr y) * indicator \<^bold>E (x, y)"
by(simp add: current_of_bipartite_def)

lemma d_OUT_current_of_bipartite:
  assumes f: "current (bipartite_web_of \<Gamma>) f"
  shows "d_OUT (current_of_bipartite f) x = d_OUT f (Inl x) - f (Inl x, Inr x)"
proof -
  have "d_OUT (current_of_bipartite f) x = \<integral>\<^sup>+ y. f (Inl x, y) * indicator \<^bold>E (x, projr y) \<partial>count_space (range Inr)"
    by(simp add: d_OUT_def nn_integral_count_space_reindex)
  also have "\<dots> = d_OUT f (Inl x) - \<integral>\<^sup>+ y. f (Inl x, y) * indicator {Inr x} y \<partial>count_space UNIV" (is "_ = _ - ?rest")
    unfolding d_OUT_def by(subst nn_integral_diff[symmetric])(auto 4 4 simp add: current_bipartite_web_finite[OF f] AE_count_space nn_integral_count_space_indicator no_loop split: split_indicator intro!: nn_integral_cong intro: currentD_outside[OF f] elim: edge_bipartite_webE)
  finally show ?thesis by simp
qed

lemma d_IN_current_of_bipartite:
  assumes f: "current (bipartite_web_of \<Gamma>) f"
  shows "d_IN (current_of_bipartite f) x = d_IN f (Inr x) - f (Inl x, Inr x)"
proof -
  have "d_IN (current_of_bipartite f) x = \<integral>\<^sup>+ y. f (y, Inr x) * indicator \<^bold>E (projl y, x) \<partial>count_space (range Inl)"
    by(simp add: d_IN_def nn_integral_count_space_reindex)
  also have "\<dots> = d_IN f (Inr x) - \<integral>\<^sup>+ y. f (y, Inr x) * indicator {Inl x} y \<partial>count_space UNIV" (is "_ = _ - ?rest")
    unfolding d_IN_def by(subst nn_integral_diff[symmetric])(auto 4 4 simp add: current_bipartite_web_finite[OF f] AE_count_space nn_integral_count_space_indicator no_loop split: split_indicator intro!: nn_integral_cong intro: currentD_outside[OF f] elim: edge_bipartite_webE)
  finally show ?thesis by simp
qed

lemma current_current_of_bipartite: \<comment> \<open>Lemma 6.3\<close>
  assumes f: "current (bipartite_web_of \<Gamma>) f" (is "current ?\<Gamma> _")
  and w: "wave (bipartite_web_of \<Gamma>) f"
  shows "current \<Gamma> (current_of_bipartite f)" (is "current _ ?f")
proof
  fix x
  have "d_OUT ?f x \<le> d_OUT f (Inl x)"
    by(simp add: d_OUT_current_of_bipartite[OF f] diff_le_self_ennreal)
  also have "\<dots> \<le> weight \<Gamma> x"
    using currentD_weight_OUT[OF f, of "Inl x"]
    by(simp split: if_split_asm)
  finally show "d_OUT ?f x \<le> weight \<Gamma> x" .
next
  fix x
  have "d_IN ?f x \<le> d_IN f (Inr x)"
    by(simp add: d_IN_current_of_bipartite[OF f] diff_le_self_ennreal)
  also have "\<dots> \<le> weight \<Gamma> x"
    using currentD_weight_IN[OF f, of "Inr x"]
    by(simp split: if_split_asm)
  finally show "d_IN ?f x \<le> weight \<Gamma> x" .
next
  have OUT: "d_OUT ?f b = 0" if "b \<in> B \<Gamma>" for b using that
    by(auto simp add: d_OUT_def nn_integral_0_iff emeasure_count_space_eq_0 intro!: currentD_outside[OF f] dest: B_out)
  show "d_OUT ?f x \<le> d_IN ?f x" if A: "x \<notin> A \<Gamma>" for x
  proof(cases "x \<in> B \<Gamma> \<or> x \<notin> \<^bold>V")
    case True
    then show ?thesis
    proof
      assume "x \<in> B \<Gamma>"
      with OUT[OF this] show ?thesis by auto
    next
      assume "x \<notin> \<^bold>V"
      hence "d_OUT ?f x = 0" by(auto simp add: d_OUT_def vertex_def nn_integral_0_iff emeasure_count_space_eq_0 intro!: currentD_outside[OF f])
      thus ?thesis by simp
    qed
  next
    case B [simplified]: False
    have "d_OUT ?f x = d_OUT f (Inl x) - f (Inl x, Inr x)" (is "_ = _ - ?rest")
      by(simp add: d_OUT_current_of_bipartite[OF f])
    also have "d_OUT f (Inl x) \<le> d_IN f (Inr x)"
    proof(rule ccontr)
      assume "\<not> ?thesis"
      hence *: "d_IN f (Inr x) < d_OUT f (Inl x)" by(simp add: not_less)
      also have "\<dots> \<le> weight \<Gamma> x" using currentD_weight_OUT[OF f, of "Inl x"] B by simp
      finally have "Inr x \<notin> TER\<^bsub>?\<Gamma>\<^esub> f" using A by(auto elim!: SAT.cases)
      moreover have "Inl x \<notin> TER\<^bsub>?\<Gamma>\<^esub> f" using * by(auto simp add: SINK.simps)
      moreover have "path ?\<Gamma> (Inl x) [Inr x] (Inr x)"
        by(rule rtrancl_path.step)(auto intro!: rtrancl_path.base simp add: no_loop A B)
      ultimately show False using waveD_separating[OF w] A B by(auto dest!: separatingD)
    qed
    hence "d_OUT f (Inl x) - ?rest \<le> d_IN f (Inr x) - ?rest" by(rule ennreal_minus_mono) simp
    also have "\<dots> =  d_IN ?f x" by(simp add: d_IN_current_of_bipartite[OF f])
    finally show ?thesis .
  qed
  show "?f e = 0" if "e \<notin> \<^bold>E" for e using that by(cases e)(auto)
qed

lemma TER_current_of_bipartite: \<comment> \<open>Lemma 6.3\<close>
  assumes f: "current (bipartite_web_of \<Gamma>) f" (is "current ?\<Gamma> _")
  and w: "wave (bipartite_web_of \<Gamma>) f"
  shows "TER (current_of_bipartite f) = separating_of_bipartite (TER\<^bsub>bipartite_web_of \<Gamma>\<^esub> f)"
    (is "TER ?f = separating_of_bipartite ?TER")
proof(rule set_eqI)
  fix x
  consider (A) "x \<in> A \<Gamma>" "x \<in> \<^bold>V" | (B) "x \<in> B \<Gamma>" "x \<in> \<^bold>V"
    | (inner) "x \<notin> A \<Gamma>" "x \<notin> B \<Gamma>" "x \<in> \<^bold>V" | (outside) "x \<notin> \<^bold>V" by auto
  thus "x \<in> TER ?f \<longleftrightarrow> x \<in> separating_of_bipartite ?TER"
  proof cases
    case A
    hence "d_OUT ?f x = d_OUT f (Inl x)" using currentD_outside[OF f, of "Inl x" "Inr x"]
      by(simp add: d_OUT_current_of_bipartite[OF f] no_loop)
    thus ?thesis using A disjoint
      by(auto simp add: separating_of_bipartite_def Let_def SINK.simps intro!: SAT.A imageI)
  next
    case B
    then have "d_IN ?f x = d_IN f (Inr x)"
      using currentD_outside[OF f, of "Inl x" "Inr x"]
      by(simp add: d_IN_current_of_bipartite[OF f] no_loop)
    moreover have "d_OUT ?f x = 0" using B currentD_outside[OF f, of "Inl x" "Inr x"]
      by(simp add: d_OUT_current_of_bipartite[OF f] no_loop)(auto simp add: d_OUT_def nn_integral_0_iff emeasure_count_space_eq_0 intro!: currentD_outside[OF f] elim!: edge_bipartite_webE dest: B_out)
    moreover have "d_OUT f (Inr x) = 0" using B disjoint by(intro currentD_OUT[OF f]) auto
    ultimately show ?thesis using B
      by(auto simp add: separating_of_bipartite_def Let_def SINK.simps SAT.simps)
  next
    case outside
    with current_current_of_bipartite[OF f w] have "d_OUT ?f x = 0" "d_IN ?f x = 0"
      by(rule currentD_outside_OUT currentD_outside_IN)+
    moreover from outside have "Inl x \<notin> vertices ?\<Gamma>" "Inr x \<notin> vertices ?\<Gamma>" by auto
    hence "d_OUT f (Inl x) = 0" "d_IN f (Inl x) = 0" "d_OUT f (Inr x) = 0" "d_IN f (Inr x) = 0"
      by(blast intro: currentD_outside_OUT[OF f] currentD_outside_IN[OF f])+
    ultimately show ?thesis using outside weight_outside[of x]
      by(auto simp add: separating_of_bipartite_def Let_def SINK.simps SAT.simps not_le)
  next
    case inner
    show ?thesis
    proof
      assume "x \<in> separating_of_bipartite ?TER"
      with inner have l: "Inl x \<in> ?TER" and r: "Inr x \<in> ?TER"
        by(auto simp add: separating_of_bipartite_def Let_def)
      have "f (Inl x, Inr x) \<le> d_OUT f (Inl x)"
        unfolding d_OUT_def by(rule nn_integral_ge_point) simp
      with l have 0: "f (Inl x, Inr x) = 0"
        by(auto simp add: SINK.simps)
      with l have "x \<in> SINK ?f"  by(simp add: SINK.simps d_OUT_current_of_bipartite[OF f])
      moreover from r have "Inr x \<in> SAT ?\<Gamma> f" by auto
      with inner have "x \<in> SAT \<Gamma> ?f"
        by(auto elim!: SAT.cases intro!: SAT.IN simp add: 0 d_IN_current_of_bipartite[OF f])
      ultimately show "x \<in> TER ?f" by simp
    next
      assume *: "x \<in> TER ?f"
      have "d_IN f (Inr x) \<le> weight ?\<Gamma> (Inr x)" using f by(rule currentD_weight_IN)
      also have "\<dots> \<le> weight \<Gamma> x" using inner by simp
      also have "\<dots> \<le> d_IN ?f x" using inner * by(auto elim: SAT.cases)
      also have "\<dots> \<le> d_IN f (Inr x)"
        by(simp add: d_IN_current_of_bipartite[OF f] max_def diff_le_self_ennreal)
      ultimately have eq: "d_IN ?f x = d_IN f (Inr x)" by simp
      hence 0: "f (Inl x, Inr x) = 0"
        using ennreal_minus_cancel_iff[of "d_IN f (Inr x)" "f (Inl x, Inr x)" 0] currentD_weight_IN[OF f, of "Inr x"] inner
          d_IN_ge_point[of f "Inl x" "Inr x"]
        by(auto simp add: d_IN_current_of_bipartite[OF f] top_unique)
      have "Inl x \<in> ?TER" "Inr x \<in> ?TER" using inner * currentD_OUT[OF f, of "Inr x"]
        by(auto simp add: SAT.simps SINK.simps d_OUT_current_of_bipartite[OF f] 0 eq)
      thus "x \<in> separating_of_bipartite ?TER" unfolding separating_of_bipartite_def Let_def by blast
    qed
  qed
qed

lemma wave_current_of_bipartite: \<comment> \<open>Lemma 6.3\<close>
  assumes f: "current (bipartite_web_of \<Gamma>) f" (is "current ?\<Gamma> _")
  and w: "wave (bipartite_web_of \<Gamma>) f"
  shows "wave \<Gamma> (current_of_bipartite f)" (is "wave _ ?f")
proof
  have sep': "separating \<Gamma> (separating_of_bipartite (TER\<^bsub>?\<Gamma>\<^esub> f))"
    by(rule separating_of_bipartite)(rule waveD_separating[OF w])
  then show sep: "separating \<Gamma> (TER (current_of_bipartite f))"
    by(simp add: TER_current_of_bipartite[OF f w])

  fix x
  assume "x \<notin> RF (TER ?f)"
  then obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>" and x: "x \<notin> TER ?f"
    and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> TER ?f"
    by(auto simp add: roofed_def elim: rtrancl_path_distinct)
  from p obtain p' where p': "path \<Gamma> x p' y" and distinct: "distinct (x # p')"
    and subset: "set p' \<subseteq> set p" by(auto elim: rtrancl_path_distinct)
  consider (outside) "x \<notin> \<^bold>V" | (A) "x \<in> A \<Gamma>" | (B) "x \<in> B \<Gamma>" | (inner) "x \<in> \<^bold>V" "x \<notin> A \<Gamma>" "x \<notin> B \<Gamma>" by auto
  then show "d_OUT ?f x = 0"
  proof cases
    case outside
    with f w show ?thesis by(rule currentD_outside_OUT[OF current_current_of_bipartite])
  next
    case A
    from separatingD[OF sep p A y] bypass have "x \<in> TER ?f" by blast
    thus ?thesis by(simp add: SINK.simps)
  next
    case B
    with f w show ?thesis by(rule currentD_OUT[OF current_current_of_bipartite])
  next
    case inner
    hence "path ?\<Gamma> (Inl x) [Inr x] (Inr x)" by(auto intro!: rtrancl_path.intros)
    from inner waveD_separating[OF w, THEN separatingD, OF this]
    consider (Inl) "Inl x \<in> TER\<^bsub>?\<Gamma>\<^esub> f" | (Inr) "Inr x \<in> TER\<^bsub>?\<Gamma>\<^esub> f" by auto
    then show ?thesis
    proof cases
      case Inl
      thus ?thesis
        by(auto simp add: SINK.simps d_OUT_current_of_bipartite[OF f] max_def)
    next
      case Inr
      with separating_of_bipartite_aux[OF waveD_separating[OF w] p y] x bypass
      have False unfolding TER_current_of_bipartite[OF f w] by blast
      thus ?thesis ..
    qed
  qed
qed

end

context countable_web begin

lemma countable_bipartite_web_of: "countable_bipartite_web (bipartite_web_of \<Gamma>)" (is "countable_bipartite_web ?\<Gamma>")
proof
  show "\<^bold>V\<^bsub>?\<Gamma>\<^esub> \<subseteq> A ?\<Gamma> \<union> B ?\<Gamma>"
    apply(rule subsetI)
    subgoal for x by(cases x) auto
    done
  show "A ?\<Gamma> \<subseteq> \<^bold>V\<^bsub>?\<Gamma>\<^esub>" by auto
  show "x \<in> A ?\<Gamma> \<and> y \<in> B ?\<Gamma>" if "edge ?\<Gamma> x y" for x y using that
    by(cases x y rule: sum.exhaust[case_product sum.exhaust])(auto simp add: inj_image_mem_iff vertex_def B_out A_in)
  show "A ?\<Gamma> \<inter> B ?\<Gamma> = {}" by auto
  show "countable \<^bold>E\<^bsub>?\<Gamma>\<^esub>" by(simp add: E_bipartite_web)
  show "weight ?\<Gamma> x \<noteq> \<top>" for x by(cases x) simp_all
  show "weight (bipartite_web_of \<Gamma>) x = 0" if "x \<notin> \<^bold>V\<^bsub>?\<Gamma>\<^esub>" for x using that
    by(cases x)(auto simp add: weight_outside)
qed

end

context web begin

lemma unhindered_bipartite_web_of:
  assumes loose: "loose \<Gamma>"
  shows "\<not> hindered (bipartite_web_of \<Gamma>)"
proof
  assume "hindered (bipartite_web_of \<Gamma>)" (is "hindered ?\<Gamma>")
  then obtain f where f: "current ?\<Gamma> f" and w: "wave ?\<Gamma> f" and hind: "hindrance ?\<Gamma> f" by cases
  from f w have "current \<Gamma> (current_of_bipartite f)" by(rule current_current_of_bipartite)
  moreover from f w have "wave \<Gamma> (current_of_bipartite f)" by(rule wave_current_of_bipartite)
  ultimately have *: "current_of_bipartite f = zero_current" by(rule looseD_wave[OF loose])
  have zero: "f (Inl x, Inr y) = 0" if "x \<noteq> y" for x y using that *[THEN fun_cong, of "(x, y)"]
     by(cases "edge \<Gamma> x y")(auto intro: currentD_outside[OF f])

  have OUT: "d_OUT f (Inl x) = f (Inl x, Inr x)" for x
  proof -
    have "d_OUT f (Inl x) = (\<Sum>\<^sup>+ y. f (Inl x, y) * indicator {Inr x} y)" unfolding d_OUT_def
      using zero currentD_outside[OF f]
      apply(intro nn_integral_cong)
      subgoal for y by(cases y)(auto split: split_indicator)
      done
    also have "\<dots> = f (Inl x, Inr x)" by simp
    finally show ?thesis .
  qed
  have IN: "d_IN f (Inr x) = f (Inl x, Inr x)" for x
  proof -
    have "d_IN f (Inr x) = (\<Sum>\<^sup>+ y. f (y, Inr x) * indicator {Inl x} y)" unfolding d_IN_def
      using zero currentD_outside[OF f]
      apply(intro nn_integral_cong)
      subgoal for y by(cases y)(auto split: split_indicator)
      done
    also have "\<dots> = f (Inl x, Inr x)" by simp
    finally show ?thesis .
  qed

  let ?TER = "TER\<^bsub>?\<Gamma>\<^esub> f"
  from hind obtain a where a: "a \<in> A ?\<Gamma>" and n\<E>: "a \<notin> \<E>\<^bsub>?\<Gamma>\<^esub> (TER\<^bsub>?\<Gamma>\<^esub> f)"
    and OUT_a: "d_OUT f a < weight ?\<Gamma> a" by cases
  from a obtain a' where a': "a = Inl a'" and v: "vertex \<Gamma> a'" and b: "a' \<notin> B \<Gamma>" by auto
  have A: "a' \<in> A \<Gamma>"
  proof(rule ccontr)
    assume A: "a' \<notin> A \<Gamma>"
    hence "edge ?\<Gamma> (Inl a') (Inr a')" using v b by simp
    hence p: "path ?\<Gamma> (Inl a') [Inr a'] (Inr a')" by(simp add: rtrancl_path_simps)
    from separatingD[OF waveD_separating[OF w] this] b v A
    have "Inl a' \<in> ?TER \<or> Inr a' \<in> ?TER" by auto
    thus False
    proof cases
      case left
      hence "d_OUT f (Inl a') = 0" by(simp add: SINK.simps)
      moreover hence "d_IN f (Inr a') = 0" by(simp add: OUT IN)
      ultimately have "Inr a' \<notin> ?TER" using v b A OUT_a a' by(auto simp add: SAT.simps)
      then have "essential ?\<Gamma> (B ?\<Gamma>) ?TER (Inl a')" using A
        by(intro essentialI[OF p]) simp_all
      with n\<E> left a' show False by simp
    next
      case right
      hence "d_IN f (Inr a') = weight \<Gamma> a'" using A by(auto simp add: currentD_SAT[OF f])
      hence "d_OUT f (Inl a') = weight \<Gamma> a'" by(simp add: IN OUT)
      with OUT_a a' b show False by simp
    qed
  qed
  moreover

  from A have "d_OUT f (Inl a') = 0" using currentD_outside[OF f, of "Inl a'" "Inr a'"]
    by(simp add: OUT no_loop)
  with b v have TER: "Inl a' \<in> ?TER" by(simp add: SAT.A SINK.simps)
  with n\<E> a' have ness: "\<not> essential ?\<Gamma> (B ?\<Gamma>) ?TER (Inl a')" by simp

  have "a' \<notin> \<E> (TER zero_current)"
  proof
    assume "a' \<in> \<E> (TER zero_current)"
    then obtain p y where p: "path \<Gamma> a' p y" and y: "y \<in> B \<Gamma>"
      and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> TER zero_current"
      by(rule \<E>_E_RF)(auto intro: roofed_greaterI)

    from p show False
    proof cases
      case base with y A disjoint show False by auto
    next
      case (step x p')
      from step(2) have "path ?\<Gamma> (Inl a') [Inr x] (Inr x)" by(simp add: rtrancl_path_simps)
      from not_essentialD[OF ness this] bypass[of x] step(1)
      have "Inr x \<in> ?TER" by simp
      with bypass[of x] step(1) have "d_IN f (Inr x) > 0"
        by(auto simp add: currentD_SAT[OF f] zero_less_iff_neq_zero)
      hence x: "Inl x \<notin> ?TER" by(auto simp add: SINK.simps OUT IN)
      from step(1) have "set (x # p') \<subseteq> set p" by auto
      with \<open>path \<Gamma> x p' y\<close> x y show False
      proof induction
        case (base x)
        thus False using currentD_outside_IN[OF f, of "Inl x"] currentD_outside_OUT[OF f, of "Inl x"]
          by(auto simp add: currentD_SAT[OF f] SINK.simps dest!: bypass)
      next
        case (step x z p' y)
        from step.prems(3) bypass[of x] weight_outside[of x] have x: "vertex \<Gamma> x" by(auto)
        from \<open>edge \<Gamma> x z\<close> have "path ?\<Gamma> (Inl x) [Inr z] (Inr z)" by(simp add: rtrancl_path_simps)
        from separatingD[OF waveD_separating[OF w] this] step.prems(1) step.prems(3) bypass[of z] x \<open>edge \<Gamma> x z\<close>
        have "Inr z \<in> ?TER" by(force simp add: B_out inj_image_mem_iff)
        with bypass[of z] step.prems(3) \<open>edge \<Gamma> x z\<close> have "d_IN f (Inr z) > 0"
          by(auto simp add: currentD_SAT[OF f] A_in zero_less_iff_neq_zero)
        hence x: "Inl z \<notin> ?TER" by(auto simp add: SINK.simps OUT IN)
        with step.IH[OF this] step.prems(2,3) show False by auto
      qed
    qed
  qed
  moreover have "d_OUT zero_current a' < weight \<Gamma> a'"
    using OUT_a a' b by (auto simp: zero_less_iff_neq_zero)
  ultimately have "hindrance \<Gamma> zero_current" by(rule hindrance)
  with looseD_hindrance[OF loose] show False by contradiction
qed

lemma (in -) divide_less_1_iff_ennreal: "a / b < (1::ennreal) \<longleftrightarrow> (0 < b \<and> a < b \<or> b = 0 \<and> a = 0 \<or> b = top)"
  by (cases a; cases b; cases "b = 0")
     (auto simp: divide_ennreal ennreal_less_iff ennreal_top_divide)

lemma linkable_bipartite_web_ofD:
  assumes link: "linkable (bipartite_web_of \<Gamma>)" (is "linkable ?\<Gamma>")
  and countable: "countable \<^bold>E"
  shows "linkable \<Gamma>"
proof -
  from link obtain f where wf: "web_flow ?\<Gamma> f" and link: "linkage ?\<Gamma> f" by blast
  from wf have f: "current ?\<Gamma> f" by(rule web_flowD_current)
  define f' where "f' = current_of_bipartite f"

  have IN_le_OUT: "d_IN f' x \<le> d_OUT f' x" if "x \<notin> B \<Gamma>" for x
  proof(cases "x \<in> \<^bold>V")
    case True
    have "d_IN f' x = d_IN f (Inr x) - f (Inl x, Inr x)" (is "_ = _ - ?rest")
      by(simp add: f'_def d_IN_current_of_bipartite[OF f])
    also have "\<dots> \<le> weight ?\<Gamma> (Inr x) - ?rest"
      using currentD_weight_IN[OF f, of "Inr x"] by(rule ennreal_minus_mono) simp
    also have "\<dots> \<le> weight ?\<Gamma> (Inl x) - ?rest" using that ennreal_minus_mono by(auto)
    also have "weight ?\<Gamma> (Inl x) = d_OUT f (Inl x)" using that linkageD[OF link, of "Inl x"] True by auto
    also have "\<dots> - ?rest = d_OUT f' x"
      by(simp add: f'_def d_OUT_current_of_bipartite[OF f])
    finally show ?thesis .
  next
    case False
    with currentD_outside_OUT[OF f, of "Inl x"] currentD_outside_IN[OF f, of "Inr x"]
    show ?thesis by(simp add: f'_def d_IN_current_of_bipartite[OF f] d_OUT_current_of_bipartite[OF f])
  qed
  have link: "linkage \<Gamma> f'"
  proof
    show "d_OUT f' a = weight \<Gamma> a" if "a \<in> A \<Gamma>" for a
    proof(cases "a \<in> \<^bold>V")
      case True
      from that have "a \<notin> B \<Gamma>" using disjoint by auto
      with that True linkageD[OF link, of "Inl a"] ennreal_minus_cancel_iff[of _ _ 0] currentD_outside[OF f, of "Inl a" "Inr a"]
      show ?thesis by(clarsimp simp add: f'_def d_OUT_current_of_bipartite[OF f] max_def no_loop)
    next
      case False
      with weight_outside[OF this] currentD_outside[OF f, of "Inl a" "Inr a"] currentD_outside_OUT[OF f, of "Inl a"]
      show ?thesis by(simp add: f'_def d_OUT_current_of_bipartite[OF f] no_loop)
    qed
  qed

  define F where "F = {g. (\<forall>e. 0 \<le> g e) \<and> (\<forall>e. e \<notin> \<^bold>E \<longrightarrow> g e = 0) \<and>
    (\<forall>x. x \<notin> B \<Gamma> \<longrightarrow> d_IN g x \<le> d_OUT g x) \<and>
    linkage \<Gamma> g \<and>
    (\<forall>x\<in>A \<Gamma>. d_IN g x = 0) \<and>
    (\<forall>x. d_OUT g x \<le> weight \<Gamma> x) \<and>
    (\<forall>x. d_IN g x \<le> weight \<Gamma> x) \<and>
    (\<forall>x\<in>B \<Gamma>. d_OUT g x = 0) \<and> g \<le> f'}"
  define leq where "leq = restrict_rel F {(f, f'). f' \<le> f}"
  have F: "Field leq = F" by(auto simp add: leq_def)
  have F_I [intro?]: "f \<in> Field leq" if "\<And>e. 0 \<le> f e" and "\<And>e. e \<notin> \<^bold>E \<Longrightarrow> f e = 0"
    and "\<And>x. x \<notin> B \<Gamma> \<Longrightarrow> d_IN f x \<le> d_OUT f x" and "linkage \<Gamma> f"
    and "\<And>x. x \<in> A \<Gamma> \<Longrightarrow> d_IN f x = 0" and "\<And>x. d_OUT f x \<le> weight \<Gamma> x"
    and "\<And>x. d_IN f x \<le> weight \<Gamma> x" and "\<And>x. x \<in> B \<Gamma> \<Longrightarrow> d_OUT f x = 0"
    and "f \<le> f'" for f using that by(simp add: F F_def)
  have F_nonneg: "0 \<le> f e" if "f \<in> Field leq" for f e using that by(cases e)(simp add: F F_def)
  have F_outside: "f e = 0" if "f \<in> Field leq" "e \<notin> \<^bold>E" for f e using that by(cases e)(simp add: F F_def)
  have F_IN_OUT: "d_IN f x \<le> d_OUT f x" if "f \<in> Field leq" "x \<notin> B \<Gamma>" for f x using that by(simp add: F F_def)
  have F_link: "linkage \<Gamma> f" if "f \<in> Field leq" for f using that by(simp add: F F_def)
  have F_IN: "d_IN f x = 0" if "f \<in> Field leq" "x \<in> A \<Gamma>" for f x using that by(simp add: F F_def)
  have F_OUT: "d_OUT f x = 0" if "f \<in> Field leq" "x \<in> B \<Gamma>" for f x using that by(simp add: F F_def)
  have F_weight_OUT: "d_OUT f x \<le> weight \<Gamma> x" if "f \<in> Field leq" for f x using that by(simp add: F F_def)
  have F_weight_IN: "d_IN f x \<le> weight \<Gamma> x" if "f \<in> Field leq" for f x using that by(simp add: F F_def)
  have F_le: "f e \<le> f' e" if "f \<in> Field leq" for f e using that by(cases e)(simp add: F F_def le_fun_def)

  have F_finite_OUT: "d_OUT f x \<noteq> \<top>" if "f \<in> Field leq" for f x
  proof -
    have "d_OUT f x \<le> weight \<Gamma> x" by(rule F_weight_OUT[OF that])
    also have "\<dots> < \<top>" by(simp add: less_top[symmetric])
    finally show ?thesis by simp
  qed

  have F_finite: "f e \<noteq> \<top>" if "f \<in> Field leq" for f e
  proof(cases e)
    case (Pair x y)
    have "f e \<le> d_OUT f x" unfolding Pair d_OUT_def by(rule nn_integral_ge_point) simp
    also have "\<dots> < \<top>" by(simp add: F_finite_OUT[OF that] less_top[symmetric])
    finally show ?thesis by simp
  qed

  have f': "f' \<in> Field leq"
  proof
    show "0 \<le> f' e" for e by(cases e)(simp add: f'_def)
    show "f' e = 0" if "e \<notin> \<^bold>E" for e using that by(clarsimp split: split_indicator_asm simp add: f'_def)
    show "d_IN f' x \<le> d_OUT f' x" if "x \<notin> B \<Gamma>" for x using that by(rule IN_le_OUT)
    show "linkage \<Gamma> f'" by(rule link)
    show "d_IN f' x = 0" if "x \<in> A \<Gamma>" for x using that currentD_IN[OF f, of "Inl x"] disjoint
      currentD_outside[OF f, of "Inl x" "Inr x"] currentD_outside_IN[OF f, of "Inr x"]
      by(cases "x \<in> \<^bold>V")(auto simp add: d_IN_current_of_bipartite[OF f] no_loop f'_def)
    show "d_OUT f' x = 0" if "x \<in> B \<Gamma>" for x using that currentD_OUT[OF f, of "Inr x"] disjoint
      currentD_outside[OF f, of "Inl x" "Inr x"] currentD_outside_OUT[OF f, of "Inl x"]
      by(cases "x \<in> \<^bold>V")(auto simp add: d_OUT_current_of_bipartite[OF f] no_loop f'_def)
    show "d_OUT f' x \<le> weight \<Gamma> x" for x using currentD_weight_OUT[OF f, of "Inl x"]
      by(simp add: d_OUT_current_of_bipartite[OF f] ennreal_diff_le_mono_left f'_def split: if_split_asm)
    show "d_IN f' x \<le> weight \<Gamma> x" for x using currentD_weight_IN[OF f, of "Inr x"]
      by(simp add: d_IN_current_of_bipartite[OF f] ennreal_diff_le_mono_left f'_def split: if_split_asm)
  qed simp

  have F_leI: "g \<in> Field leq" if f: "f \<in> Field leq" and le: "\<And>e. g e \<le> f e"
    and nonneg: "\<And>e. 0 \<le> g e" and IN_OUT: "\<And>x. x \<notin> B \<Gamma> \<Longrightarrow> d_IN g x \<le> d_OUT g x"
    and link: "linkage \<Gamma> g"
    for f g
  proof
    show "g e = 0" if "e \<notin> \<^bold>E" for e using nonneg[of e] F_outside[OF f that] le[of e] by simp
    show "d_IN g a = 0" if "a \<in> A \<Gamma>" for a
      using d_IN_mono[of g a f, OF le] F_IN[OF f that] by auto
    show "d_OUT g b = 0" if "b \<in> B \<Gamma>" for b
      using d_OUT_mono[of g b f, OF le] F_OUT[OF f that] by auto
    show "d_OUT g x \<le> weight \<Gamma> x" for x
      using d_OUT_mono[of g x f, OF le] F_weight_OUT[OF f] by(rule order_trans)
    show "d_IN g x \<le> weight \<Gamma> x" for x
      using d_IN_mono[of g x f, OF le] F_weight_IN[OF f] by(rule order_trans)
    show "g \<le> f'" using order_trans[OF le F_le[OF f]] by(auto simp add: le_fun_def)
  qed(blast intro: IN_OUT link nonneg)+

  have chain_Field: "Inf M \<in> F" if M: "M \<in> Chains leq" and nempty: "M \<noteq> {}" for M
  proof -
    from nempty obtain g0 where g0_in_M: "g0 \<in> M" by auto
    with M have g0: "g0 \<in> Field leq" by(rule Chains_FieldD)

    from M have "M \<in> Chains {(g, g'). g' \<le> g}"
      by(rule mono_Chains[THEN subsetD, rotated])(auto simp add: leq_def in_restrict_rel_iff)
    then have "Complete_Partial_Order.chain (\<ge>) M" by(rule Chains_into_chain)
    hence chain': "Complete_Partial_Order.chain (\<le>) M" by(simp add: chain_dual)

    have "support_flow f' \<subseteq> \<^bold>E" using F_outside[OF f'] by(auto intro: ccontr simp add: support_flow.simps)
    then have countable': "countable (support_flow f')"
      by(rule countable_subset)(simp add: E_bipartite_web countable "\<^bold>V_def")

    have finite_OUT: "d_OUT f' x \<noteq> \<top>" for x using weight_finite[of x]
      by(rule neq_top_trans)(rule F_weight_OUT[OF f'])
    have finite_IN: "d_IN f' x \<noteq> \<top>" for x using weight_finite[of x]
      by(rule neq_top_trans)(rule F_weight_IN[OF f'])
    have OUT_M: "d_OUT (Inf M) x = (INF g\<in>M. d_OUT g x)" for x using chain' nempty countable' _ finite_OUT
      by(rule d_OUT_Inf)(auto dest!: Chains_FieldD[OF M] simp add: leq_def F_nonneg F_le)
    have IN_M: "d_IN (Inf M) x = (INF g\<in>M. d_IN g x)" for x using chain' nempty countable' _ finite_IN
      by(rule d_IN_Inf)(auto dest!: Chains_FieldD[OF M] simp add: leq_def F_nonneg F_le)

    show "Inf M \<in> F" using g0 unfolding F[symmetric]
    proof(rule F_leI)
      show "(Inf M) e \<le> g0 e" for e using g0_in_M by(auto intro: INF_lower)
      show "0 \<le> (Inf M) e" for e by(auto intro!: INF_greatest dest: F_nonneg dest!: Chains_FieldD[OF M])
      show "d_IN (Inf M) x \<le> d_OUT (Inf M) x" if "x \<notin> B \<Gamma>" for x using that
        by(auto simp add: IN_M OUT_M intro!: INF_mono dest: Chains_FieldD[OF M] intro: F_IN_OUT[OF _ that])
      show "linkage \<Gamma> (Inf M)" using nempty
        by(simp add: linkage.simps OUT_M F_link[THEN linkageD] Chains_FieldD[OF M] cong: INF_cong)
    qed
  qed

  let ?P = "\<lambda>g z. z \<notin> A \<Gamma> \<and> z \<notin> B \<Gamma> \<and> d_OUT g z > d_IN g z"

  define link
    where "link g =
      (if \<exists>z. ?P g z then
        let z = SOME z. ?P g z; factor = d_IN g z / d_OUT g z
        in (\<lambda>(x, y). (if x = z then factor else 1) * g (x, y))
       else g)" for g
  have increasing: "link g \<le> g \<and> link g \<in> Field leq" if g: "g \<in> Field leq" for g
  proof(cases "\<exists>z. ?P g z")
    case False
    thus ?thesis using that by(auto simp add: link_def leq_def)
  next
    case True
    define z where "z = Eps (?P g)"
    from True have "?P g z" unfolding z_def by(rule someI_ex)
    hence A: "z \<notin> A \<Gamma>" and B: "z \<notin> B \<Gamma>" and less: "d_IN g z < d_OUT g z" by simp_all
    let ?factor = "d_IN g z / d_OUT g z"
    have link [simp]: "link g (x, y) = (if x = z then ?factor else 1) * g (x, y)" for x y
      using True by(auto simp add: link_def z_def Let_def)

    have "?factor \<le> 1" (is "?factor \<le> _") using less
      by(cases "d_OUT g z" "d_IN g z" rule: ennreal2_cases) (simp_all add: ennreal_less_iff divide_ennreal)
    hence le': "?factor * g (x, y) \<le> 1 * g (x, y)" for y x
      by(rule mult_right_mono)(simp add: F_nonneg[OF g])
    hence le: "link g e \<le> g e" for e by(cases e)simp
    have "link g \<in> Field leq" using g le
    proof(rule F_leI)
      show nonneg: "0 \<le> link g e" for e
        using F_nonneg[OF g, of e] by(cases e) simp
      show "linkage \<Gamma> (link g)" using that A F_link[OF g] by(clarsimp simp add: linkage.simps d_OUT_def)

      fix x
      assume x: "x \<notin> B \<Gamma>"
      have "d_IN (link g) x \<le> d_IN g x" unfolding d_IN_def using le' by(auto intro: nn_integral_mono)
      also have "\<dots> \<le> d_OUT (link g) x"
      proof(cases "x = z")
        case True
        have "d_IN g x = d_OUT (link g) x" unfolding d_OUT_def
          using True F_weight_IN[OF g, of x] F_IN_OUT[OF g x] F_finite_OUT F_finite_OUT[OF g, of x]
          by(cases "d_OUT g z = 0")
            (auto simp add: nn_integral_divide nn_integral_cmult d_OUT_def[symmetric] ennreal_divide_times less_top)
        thus ?thesis by simp
      next
        case False
        have "d_IN g x \<le> d_OUT g x" using x by(rule F_IN_OUT[OF g])
        also have "\<dots> \<le> d_OUT (link g) x" unfolding d_OUT_def using False by(auto intro!: nn_integral_mono)
        finally show ?thesis .
      qed
      finally show "d_IN (link g) x \<le> d_OUT (link g) x" .
    qed
    with le g show ?thesis unfolding F by(simp add: leq_def le_fun_def del: link)
  qed

  have "bourbaki_witt_fixpoint Inf leq link" using chain_Field increasing unfolding leq_def
    by(intro bourbaki_witt_fixpoint_restrict_rel)(auto intro: Inf_greatest Inf_lower)
  then interpret bourbaki_witt_fixpoint Inf leq link .

  define g where "g = fixp_above f'"

  have g: "g \<in> Field leq" using f' unfolding g_def by(rule fixp_above_Field)
  hence "linkage \<Gamma> g" by(rule F_link)
  moreover
  have "web_flow \<Gamma> g"
  proof(intro web_flow.intros current.intros)
    show "d_OUT g x \<le> weight \<Gamma> x" for x using g by(rule F_weight_OUT)
    show "d_IN g x \<le> weight \<Gamma> x" for x using g by(rule F_weight_IN)
    show "d_IN g x = 0" if "x \<in> A \<Gamma>" for x using g that by(rule F_IN)
    show B: "d_OUT g x = 0" if "x \<in> B \<Gamma>" for x using g that by(rule F_OUT)
    show "g e = 0" if "e \<notin> \<^bold>E" for e using g that by(rule F_outside)

    show KIR: "KIR g x" if A: "x \<notin> A \<Gamma>" and B: "x \<notin> B \<Gamma>" for x
    proof(rule ccontr)
      define z where "z = Eps (?P g)"
      assume "\<not> KIR g x"
      with F_IN_OUT[OF g B] have "d_OUT g x > d_IN g x" by simp
      with A B have Ex: "\<exists>x. ?P g x" by blast
      then have "?P g z" unfolding z_def by(rule someI_ex)
      hence A: "z \<notin> A \<Gamma>" and B: "z \<notin> B \<Gamma>" and less: "d_IN g z < d_OUT g z" by simp_all
      let ?factor = "d_IN g z / d_OUT g z"
      have "\<exists>y. edge \<Gamma> z y \<and> g (z, y) > 0"
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence "d_OUT g z = 0" using F_outside[OF g]
          by(force simp add: d_OUT_def nn_integral_0_iff_AE AE_count_space not_less)
        with less show False by simp
      qed
      then obtain y where y: "edge \<Gamma> z y" and gr0: "g (z, y) > 0" by blast
      have "?factor < 1" (is "?factor < _") using less
        by(cases "d_OUT g z" "d_IN g z" rule: ennreal2_cases)
          (auto simp add: ennreal_less_iff divide_ennreal)

      hence le': "?factor * g (z, y) < 1 * g (z, y)" using gr0 F_finite[OF g]
        by(intro ennreal_mult_strict_right_mono) (auto simp: less_top)
      hence "link g (z, y) \<noteq> g (z, y)" using Ex by(auto simp add: link_def z_def Let_def)
      hence "link g \<noteq> g" by(auto simp add: fun_eq_iff)
      moreover have "link g = g" using f' unfolding g_def by(rule fixp_above_unfold[symmetric])
      ultimately show False by contradiction
    qed
    show "d_OUT g x \<le> d_IN g x" if "x \<notin> A \<Gamma>" for x using KIR[of x] that B[of x]
      by(cases "x \<in> B \<Gamma>") auto
  qed
  ultimately show ?thesis by blast
qed

end

subsection \<open>Extending a wave by a linkage\<close>

lemma linkage_quotient_webD:
  fixes \<Gamma> :: "('v, 'more) web_scheme" (structure) and h g
  defines "k \<equiv> plus_current h g"
  assumes f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  and wg: "web_flow (quotient_web \<Gamma> f) g" (is "web_flow ?\<Gamma> _")
  and link: "linkage (quotient_web \<Gamma> f) g"
  and trim: "trimming \<Gamma> f h"
  shows "web_flow \<Gamma> k"
  and "orthogonal_current \<Gamma> k (\<E> (TER f))"
proof -
  from wg have g: "current ?\<Gamma> g" by(rule web_flowD_current)

  from trim obtain h: "current \<Gamma> h" and w': "wave \<Gamma> h" and h_le_f: "\<And>e. h e \<le> f e"
    and KIR: "\<And>x. \<lbrakk>x \<in> RF\<^sup>\<circ> (TER f); x \<notin> A \<Gamma>\<rbrakk> \<Longrightarrow> KIR h x"
    and TER: "TER h \<supseteq> \<E> (TER f) - A \<Gamma>"
    by(cases)(auto simp add: le_fun_def)

  have eq: "quotient_web \<Gamma> f = quotient_web \<Gamma> h" using w trim by(rule quotient_web_trimming)

  let ?T = "\<E> (TER f)"

  have RFc: "RF\<^sup>\<circ> (TER h) = RF\<^sup>\<circ> (TER f)"
    by(subst (1 2) roofed_circ_essential[symmetric])(simp only: trimming_\<E>[OF w trim])
  have OUT_k: "d_OUT k x = (if x \<in> RF\<^sup>\<circ> (TER f) then d_OUT h x else d_OUT g x)" for x
    using OUT_plus_current[OF h w', of g] web_flowD_current[OF wg] unfolding eq k_def RFc by simp
  have RF: "RF (TER h) = RF (TER f)"
    by(subst (1 2) RF_essential[symmetric])(simp only: trimming_\<E>[OF w trim])
  have IN_k: "d_IN k x = (if x \<in> RF (TER f) then d_IN h x else d_IN g x)" for x
    using IN_plus_current[OF h w', of g] web_flowD_current[OF wg] unfolding eq k_def RF by simp

  have k: "current \<Gamma> k" unfolding k_def using h w' g unfolding eq by(rule current_plus_current)
  then show wk: "web_flow \<Gamma> k"
  proof(rule web_flow)
    fix x
    assume "x \<in> \<^bold>V" and A: "x \<notin> A \<Gamma>" and B: "x \<notin> B \<Gamma>"
    show "KIR k x"
    proof(cases "x \<in> \<E> (TER f)")
      case False
      thus ?thesis using A KIR[of x] web_flowD_KIR[OF wg, of x] B by(auto simp add: OUT_k IN_k roofed_circ_def)
    next
      case True
      with A TER have [simp]: "d_OUT h x = 0" and "d_IN h x \<ge> weight \<Gamma> x"
        by(auto simp add: SINK.simps elim: SAT.cases)
      with currentD_weight_IN[OF h, of x] have [simp]: "d_IN h x = weight \<Gamma> x" by auto
      from linkageD[OF link, of x] True currentD_IN[OF g, of x] B
      have "d_OUT g x = weight \<Gamma> x" "d_IN g x = 0" by(auto simp add: roofed_circ_def)
      thus ?thesis using True by(auto simp add: IN_k OUT_k roofed_circ_def intro: roofed_greaterI)
    qed
  qed

  have h_le_k: "h e \<le> k e" for e unfolding k_def plus_current_def by(rule add_increasing2) simp_all
  hence "SAT \<Gamma> h \<subseteq> SAT \<Gamma> k" by(rule SAT_mono)
  hence SAT: "?T \<subseteq> SAT \<Gamma> k" using TER by(auto simp add: elim!: SAT.cases intro: SAT.intros)
  show "orthogonal_current \<Gamma> k ?T"
  proof(rule orthogonal_current)
    show "weight \<Gamma> x \<le> d_IN k x" if "x \<in> ?T" "x \<notin> A \<Gamma>" for x
      using subsetD[OF SAT, of x] that by(auto simp add: currentD_SAT[OF k])
  next
    fix x
    assume x: "x \<in> ?T" and A: "x \<in> A \<Gamma>" and B: "x \<notin> B \<Gamma>"
    with d_OUT_mono[of h x f, OF h_le_f] have "d_OUT h x = 0" by(auto simp add: SINK.simps)
    moreover from linkageD[OF link, of x] x A have "d_OUT g x = weight ?\<Gamma> x" by simp
    ultimately show "d_OUT k x = weight \<Gamma> x" using x A currentD_IN[OF f A] B
      by(auto simp add: d_OUT_add roofed_circ_def k_def plus_current_def )
  next
    fix u v
    assume v: "v \<in> RF ?T" and u: "u \<notin> RF\<^sup>\<circ> ?T"
    have "h (u, v) \<le> f (u, v)" by(rule h_le_f)
    also have "\<dots> \<le> d_OUT f u" unfolding d_OUT_def by(rule nn_integral_ge_point) simp
    also have "\<dots> = 0" using u using RF_essential[of \<Gamma> "TER f"]
      by(auto simp add: roofed_circ_def SINK.simps intro: waveD_OUT[OF w])
    finally have "h (u, v) = 0" by simp
    moreover have "g (u, v) = 0" using g v RF_essential[of \<Gamma> "TER f"]
      by(auto intro: currentD_outside simp add: roofed_circ_def)
    ultimately show "k (u, v) = 0" by(simp add: k_def)
  qed
qed

context countable_web begin

lemma ex_orthogonal_current': \<comment> \<open>Lemma 4.15\<close>
  assumes loose_linkable: "\<And>f. \<lbrakk> current \<Gamma> f; wave \<Gamma> f; loose (quotient_web \<Gamma> f) \<rbrakk> \<Longrightarrow> linkable (quotient_web \<Gamma> f)"
  shows "\<exists>f S. web_flow \<Gamma> f \<and> separating \<Gamma> S \<and> orthogonal_current \<Gamma> f S"
proof -
  from ex_maximal_wave[OF countable]
  obtain f where f: "current \<Gamma> f"
    and w: "wave \<Gamma> f"
    and maximal: "\<And>w. \<lbrakk> current \<Gamma> w; wave \<Gamma> w; f \<le> w \<rbrakk> \<Longrightarrow> f = w" by blast
  from ex_trimming[OF f w countable weight_finite] obtain h where h: "trimming \<Gamma> f h" ..

  let ?\<Gamma> = "quotient_web \<Gamma> f"
  interpret \<Gamma>: countable_web "?\<Gamma>" by(rule countable_web_quotient_web)
  have "loose ?\<Gamma>" using f w maximal by(rule loose_quotient_web[OF  weight_finite])
  with f w have "linkable ?\<Gamma>" by(rule loose_linkable)
  then obtain g where wg: "web_flow ?\<Gamma> g" and link: "linkage ?\<Gamma> g" by blast

  let ?k = "plus_current h g"
  have "web_flow \<Gamma> ?k" "orthogonal_current \<Gamma> ?k (\<E> (TER f))"
    by(rule linkage_quotient_webD[OF f w wg link h])+
  moreover have "separating \<Gamma> (\<E> (TER f))"
    using waveD_separating[OF w] by(rule separating_essential)
  ultimately show ?thesis by blast
qed

end

subsection \<open>From a network to a web\<close>

definition web_of_network :: "('v, 'more) network_scheme \<Rightarrow> ('v edge, 'more) web_scheme"
where
  "web_of_network \<Delta> =
   \<lparr>edge = \<lambda>(x, y) (y', z). y' = y \<and> edge \<Delta> x y \<and> edge \<Delta> y z,
    weight = capacity \<Delta>,
    A = {(source \<Delta>, x)|x. edge \<Delta> (source \<Delta>) x},
    B = {(x, sink \<Delta>)|x. edge \<Delta> x (sink \<Delta>)},
    \<dots> = network.more \<Delta>\<rparr>"

lemma web_of_network_sel [simp]:
  fixes \<Delta> (structure) shows
  "edge (web_of_network \<Delta>) e e' \<longleftrightarrow> e \<in> \<^bold>E \<and> e' \<in> \<^bold>E \<and> snd e = fst e'"
  "weight (web_of_network \<Delta>) e = capacity \<Delta> e"
  "A (web_of_network \<Delta>) = {(source \<Delta>, x)|x. edge \<Delta> (source \<Delta>) x}"
  "B (web_of_network \<Delta>) = {(x, sink \<Delta>)|x. edge \<Delta> x (sink \<Delta>)}"
by(auto simp add: web_of_network_def split: prod.split)

lemma vertex_web_of_network [simp]:
  "vertex (web_of_network \<Delta>) (x, y) \<longleftrightarrow> edge \<Delta> x y \<and> (\<exists>z. edge \<Delta> y z \<or> edge \<Delta> z x)"
by(auto simp add: vertex_def Domainp.simps Rangep.simps)

definition flow_of_current :: "('v, 'more) network_scheme \<Rightarrow> 'v edge current \<Rightarrow> 'v flow"
where "flow_of_current \<Delta> f e = max (d_OUT f e) (d_IN f e)"

lemma flow_flow_of_current:
  fixes \<Delta> (structure) and \<Gamma>
  defines [simp]: "\<Gamma> \<equiv> web_of_network \<Delta>"
  assumes fw: "web_flow \<Gamma> f"
  shows "flow \<Delta> (flow_of_current \<Delta> f)" (is "flow _ ?f")
proof
  from fw have f: "current \<Gamma> f" and KIR: "\<And>x. \<lbrakk> x \<notin> A \<Gamma>; x \<notin> B \<Gamma> \<rbrakk> \<Longrightarrow> KIR f x"
    by(auto 4 3 dest: web_flowD_current web_flowD_KIR)

  show "?f e \<le> capacity \<Delta> e" for e
    using currentD_weight_OUT[OF f, of e] currentD_weight_IN[OF f, of e]
    by(simp add: flow_of_current_def)

  fix x
  assume x: "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>"
  have "d_OUT ?f x = (\<Sum>\<^sup>+ y. d_IN f (x, y))" unfolding d_OUT_def
    by(simp add: flow_of_current_def max_absorb2 currentD_OUT_IN[OF f] x)
  also have "\<dots> = (\<Sum>\<^sup>+ y. \<Sum>\<^sup>+ e\<in>range (\<lambda>z. (z, x)). f (e, x, y))"
    by(auto simp add: nn_integral_count_space_indicator d_IN_def intro!: nn_integral_cong currentD_outside[OF f] split: split_indicator)
  also have "\<dots> = (\<Sum>\<^sup>+ z\<in>UNIV. \<Sum>\<^sup>+ y. f ((z, x), x, y))"
    by(subst nn_integral_snd_count_space[of "case_prod _", simplified])
      (simp add: nn_integral_count_space_reindex nn_integral_fst_count_space[of "case_prod _", simplified])
  also have "\<dots> = (\<Sum>\<^sup>+ z. \<Sum>\<^sup>+ e\<in>range (Pair x). f ((z, x), e))"
    by(simp add: nn_integral_count_space_reindex)
  also have "\<dots> = (\<Sum>\<^sup>+ z. d_OUT f (z, x))"
    by(auto intro!: nn_integral_cong currentD_outside[OF f] simp add: d_OUT_def nn_integral_count_space_indicator split: split_indicator)
  also have "\<dots> = (\<Sum>\<^sup>+ z\<in>{z. edge \<Delta> z x}. d_OUT f (z, x))"
    by(auto intro!: nn_integral_cong currentD_outside_OUT[OF f] simp add: nn_integral_count_space_indicator split: split_indicator)
  also have "\<dots> = (\<Sum>\<^sup>+ z\<in>{z. edge \<Delta> z x}. max (d_OUT f (z, x)) (d_IN f (z, x)))"
  proof(rule nn_integral_cong)
    show "d_OUT f (z, x) = max (d_OUT f (z, x)) (d_IN f (z, x))"
      if "z \<in> space (count_space {z. edge \<Delta> z x})" for z using currentD_IN[OF f] that
      by(cases "z = source \<Delta>")(simp_all add: max_absorb1  currentD_IN[OF f] KIR x)
  qed
  also have "\<dots> = (\<Sum>\<^sup>+ z. max (d_OUT f (z, x)) (d_IN f (z, x)))"
    by(auto intro!: nn_integral_cong currentD_outside_OUT[OF f] currentD_outside_IN[OF f] simp add: nn_integral_count_space_indicator max_def split: split_indicator)
  also have "\<dots> = d_IN ?f x" by(simp add: flow_of_current_def d_IN_def)
  finally show "KIR ?f x" .
qed

text \<open>
  The reduction of Conjecture 1.2 to Conjecture 3.6 is flawed in @{cite "AharoniBergerGeorgakopoulusPerlsteinSpruessel2011JCT"}.
  Not every essential A-B separating set of vertices in @{term "web_of_network \<Delta>"} is an s-t-cut in
  @{term \<Delta>}, as the following counterexample shows.

  The network @{term \<Delta>} has five nodes @{term "s"}, @{term "t"}, @{term "x"}, @{term "y"} and @{term "z"}
  and edges @{term "(s, x)"}, @{term "(x, y)"}, @{term "(y, z)"}, @{term "(y, t)"} and @{term "(z, t)"}.
  For @{term "web_of_network \<Delta>"}, the set @{term "S = {(x, y), (y, z)}"} is essential and A-B separating.
  (@{term "(x, y)"} is essential due to the path @{term "[(y, z)]"} and @{term "(y, z)"} is essential
  due to the path @{term "[(z, t)]"}). However, @{term S} is not a cut in @{term \<Delta>} because the node @{term y}
  has an outgoing edge that is in @{term S} and one that is not in @{term S}.

  However, this can be remedied if all edges carry positive capacity. Then, orthogonality of the current
  rules out the above possibility.
\<close>
lemma cut_RF_separating:
  fixes \<Delta> (structure)
  assumes sep: "separating_network \<Delta> V"
  and sink: "sink \<Delta> \<notin> V"
  shows "cut \<Delta> (RF\<^sup>N V)"
proof
  show "source \<Delta> \<in> RF\<^sup>N V" by(rule roofedI)(auto dest: separatingD[OF sep])
  show "sink \<Delta> \<notin> RF\<^sup>N V" using sink by(auto dest: roofedD[OF _ rtrancl_path.base])
qed

context
  fixes \<Delta> :: "('v, 'more) network_scheme" and \<Gamma> (structure)
  defines \<Gamma>_def: "\<Gamma> \<equiv> web_of_network \<Delta>"
begin

lemma separating_network_cut_of_sep:
  assumes sep: "separating \<Gamma> S"
  and source_sink: "source \<Delta> \<noteq> sink \<Delta>"
  shows "separating_network \<Delta> (fst ` \<E> S)"
proof
  define s t where "s = source \<Delta>" and "t = sink \<Delta>"
  fix p
  assume p: "path \<Delta> s p t"
  with p source_sink have "p \<noteq> []" by cases(auto simp add: s_def t_def)
  with p have p': "path \<Gamma> (s, hd p) (zip p (tl p)) (last (s # butlast p), t)"
  proof(induction)
    case (step x y p z)
    then show ?case by(cases p)(auto elim: rtrancl_path.cases intro: rtrancl_path.intros simp add: \<Gamma>_def)
  qed simp
  from sep have "separating \<Gamma> (\<E> S)" by(rule separating_essential)
  from this p' have "(\<exists>z\<in>set (zip p (tl p)). z \<in> \<E> S) \<or> (s, hd p) \<in> \<E> S"
    apply(rule separatingD)
    using rtrancl_path_nth[OF p, of 0] rtrancl_path_nth[OF p, of "length p - 1"] \<open>p \<noteq> []\<close> rtrancl_path_last[OF p]
    apply(auto simp add: \<Gamma>_def s_def t_def hd_conv_nth last_conv_nth nth_butlast nth_Cons' cong: if_cong split: if_split_asm)
    apply(metis One_nat_def Suc_leI cancel_comm_monoid_add_class.diff_cancel le_antisym length_butlast length_greater_0_conv list.size(3))+
    done
  then show "(\<exists>z\<in>set p. z \<in> fst ` \<E> S) \<or> s \<in> fst ` \<E> S"
    by(auto dest!: set_zip_leftD intro: rev_image_eqI)
qed

definition cut_of_sep :: "('v \<times> 'v) set \<Rightarrow> 'v set"
where "cut_of_sep S = RF\<^sup>N\<^bsub>\<Delta>\<^esub> (fst ` \<E> S)"

lemma separating_cut:
  assumes sep: "separating \<Gamma> S"
  and neq: "source \<Delta> \<noteq> sink \<Delta>"
  and sink_out: "\<And>x. \<not> edge \<Delta> (sink \<Delta>) x"
  shows "cut \<Delta> (cut_of_sep S)"
  unfolding cut_of_sep_def
proof(rule cut_RF_separating)
  show "separating_network \<Delta> (fst ` \<E> S)" using sep neq by(rule separating_network_cut_of_sep)

  show "sink \<Delta> \<notin> fst ` \<E> S"
  proof
    assume "sink \<Delta> \<in> fst ` \<E> S"
    then obtain x where "(sink \<Delta>, x) \<in> \<E> S" by auto
    hence "(sink \<Delta>, x) \<in> \<^bold>V" by(auto simp add: \<Gamma>_def dest!: essential_vertex)
    then show False by(simp add: \<Gamma>_def sink_out)
  qed
qed

context
  fixes f :: "'v edge current" and S
  assumes wf: "web_flow \<Gamma> f"
  and ortho: "orthogonal_current \<Gamma> f S"
  and sep: "separating \<Gamma> S"
  and capacity_pos: "\<And>e. e \<in> \<^bold>E\<^bsub>\<Delta>\<^esub> \<Longrightarrow> capacity \<Delta> e > 0"
begin

private lemma f: "current \<Gamma> f" using wf by(rule web_flowD_current)

lemma orthogonal_leave_RF:
  assumes e: "edge \<Delta> x y"
  and x: "x \<in> (cut_of_sep S)"
  and y: "y \<notin> (cut_of_sep S)"
  shows "(x, y) \<in> S"
proof -
  from y obtain p where p: "path \<Delta> y p (sink \<Delta>)" and y': "y \<notin> fst ` \<E> S"
    and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> fst ` \<E> S" by(auto simp add: roofed_def cut_of_sep_def \<Gamma>_def[symmetric])
  from e p have p': "path \<Delta> x (y # p) (sink \<Delta>)" ..
  from roofedD[OF x[unfolded cut_of_sep_def] this] y' bypass have "x \<in> fst ` \<E> S" by(auto simp add: \<Gamma>_def[symmetric])
  then obtain z where xz: "(x, z) \<in> \<E> S" by auto
  then obtain q b where q: "path \<Gamma> (x, z) q b" and b: "b \<in> B \<Gamma>"
    and distinct: "distinct ((x, z) # q)" and bypass': "\<And>z. z \<in> set q \<Longrightarrow> z \<notin> RF S"
    by(rule \<E>_E_RF) blast

  define p' where "p' = y # p"
  hence "p' \<noteq> []" by simp
  with p' have "path \<Gamma> (x, hd p') (zip p' (tl p')) (last (x # butlast p'), sink \<Delta>)"
    unfolding p'_def[symmetric]
  proof(induction)
    case (step x y p z)
    then show ?case
      by(cases p)(auto elim: rtrancl_path.cases intro: rtrancl_path.intros simp add: \<Gamma>_def)
  qed simp
  then have p'': "path \<Gamma> (x, y) (zip (y # p) p) (last (x # butlast (y # p)), sink \<Delta>)" (is "path _ ?y ?p ?t")
    by(simp add: p'_def)
  have "(?y # ?p) ! length p = ?t" using rtrancl_path_last[OF p'] p rtrancl_path_last[OF p]
    apply(auto split: if_split_asm simp add: nth_Cons butlast_conv_take take_Suc_conv_app_nth split: nat.split elim: rtrancl_path.cases)
    apply(simp add: last_conv_nth)
    done
  moreover have "length p < length (?y # ?p)" by simp
  ultimately have t: "?t \<in> B \<Gamma>" using rtrancl_path_nth[OF p'', of "length p - 1"] e
    by(cases p)(simp_all add: \<Gamma>_def split: if_split_asm)

  show S: "(x, y) \<in> S"
  proof(cases "x = source \<Delta>")
    case True
    from separatingD[OF separating_essential, OF sep p'' _ t] e True
    consider (z) z z' where "(z, z') \<in> set ?p" "(z, z') \<in> \<E> S" | "(x, y) \<in> S" by(auto simp add: \<Gamma>_def)
    thus ?thesis
    proof cases
      case (z z)
      hence "z \<in> set p" "z \<in> fst ` \<E> S"
        using y' by(auto dest!: set_zip_leftD intro: rev_image_eqI)
      hence False by(auto dest: bypass)
      thus ?thesis ..
    qed
  next
    case False
    have "\<exists>e. edge \<Gamma> e (x, z) \<and> f (e, (x, z)) > 0"
    proof(rule ccontr)
      assume "\<not> ?thesis"
      then have "d_IN f (x, z) = 0" unfolding d_IN_def using currentD_outside[OF f, of _ "(x, z)"]
        by(force simp add: nn_integral_0_iff_AE AE_count_space not_less)
      moreover
      from xz have "(x, z) \<in> S" by auto
      hence "(x, z) \<in> SAT \<Gamma> f" by(rule orthogonal_currentD_SAT[OF ortho])
      with False have "d_IN f (x, z) \<ge> capacity \<Delta> (x, z)" by(auto simp add: SAT.simps \<Gamma>_def)
      ultimately have "\<not> capacity \<Delta> (x, z) > 0" by auto
      hence "\<not> edge \<Delta> x z" using capacity_pos[of "(x, z)"] by auto
      moreover with q have "b = (x, z)" by cases(auto simp add: \<Gamma>_def)
      with b have "edge \<Delta> x z" by(simp add: \<Gamma>_def)
      ultimately show False by contradiction
    qed
    then obtain u where ux: "edge \<Delta> u x" and xz': "edge \<Delta> x z" and uxz: "edge \<Gamma> (u, x) (x, z)"
      and gt0: "f ((u, x), (x, z)) > 0" by(auto simp add: \<Gamma>_def)
    have "(u, x) \<in> RF\<^sup>\<circ> S" using orthogonal_currentD_in[OF ortho, of "(x, z)" "(u, x)"] gt0 xz
      by(fastforce intro: roofed_greaterI)
    hence ux_RF: "(u, x) \<in> RF (\<E> S)" and ux_\<E>: "(u, x) \<notin> \<E> S" unfolding RF_essential by(simp_all add: roofed_circ_def)

    from ux e have "edge \<Gamma> (u, x) (x, y)" by(simp add: \<Gamma>_def)
    hence "path \<Gamma> (u, x) ((x, y) # ?p) ?t" using p'' ..
    from roofedD[OF ux_RF this t] ux_\<E>
    consider "(x, y) \<in> S" | (z) z z' where "(z, z') \<in> set ?p" "(z, z') \<in> \<E> S" by auto
    thus ?thesis
    proof cases
      case (z z)
      with bypass[of z] y' have False by(fastforce dest!: set_zip_leftD intro: rev_image_eqI)
      thus ?thesis ..
    qed
  qed
qed

lemma orthogonal_flow_of_current:
  assumes source_sink: "source \<Delta> \<noteq> sink \<Delta>"
  and sink_out: "\<And>x. \<not> edge \<Delta> (sink \<Delta>) x"
  and no_direct_edge: "\<not> edge \<Delta> (source \<Delta>) (sink \<Delta>)" \<comment> \<open>Otherwise, @{const A} and @{const B} of the web would not be disjoint.\<close>
  shows "orthogonal \<Delta> (flow_of_current \<Delta> f) (cut_of_sep S)" (is "orthogonal _ ?f ?S")
proof
  fix x y
  assume e: "edge \<Delta> x y" and "x \<in> ?S" and "y \<notin> ?S"
  then have S: "(x, y) \<in> S"by(rule orthogonal_leave_RF)

  show "?f (x, y) = capacity \<Delta> (x, y)"
  proof(cases "x = source \<Delta>")
    case False
    with orthogonal_currentD_SAT[OF ortho S]
    have "weight \<Gamma> (x, y) \<le> d_IN f (x, y)" by cases(simp_all add: \<Gamma>_def)
    with False currentD_OUT_IN[OF f, of "(x, y)"] currentD_weight_IN[OF f, of "(x, y)"]
    show ?thesis by(simp add: flow_of_current_def \<Gamma>_def max_def)
  next
    case True
    with orthogonal_currentD_A[OF ortho S] e currentD_weight_IN[OF f, of "(x, y)"] no_direct_edge
    show ?thesis by(auto simp add: flow_of_current_def \<Gamma>_def max_def)
  qed
next
  from sep source_sink sink_out have cut: "cut \<Delta> ?S" by(rule separating_cut)

  fix x y
  assume xy: "edge \<Delta> x y"
    and x: "x \<notin> ?S"
    and y: "y \<in> ?S"
  from x obtain p where p: "path \<Delta> x p (sink \<Delta>)" and x': "x \<notin> fst ` \<E> S"
    and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> fst ` \<E> S" by(auto simp add: roofed_def cut_of_sep_def)
  have source: "x \<noteq> source \<Delta>"
  proof
    assume "x = source \<Delta>"
    have "separating_network \<Delta> (fst ` \<E> S)" using sep source_sink by(rule separating_network_cut_of_sep)
    from separatingD[OF this p] \<open>x = source \<Delta>\<close> x show False
      by(auto dest: bypass intro: roofed_greaterI simp add: cut_of_sep_def)
  qed
  hence A: "(x, y) \<notin> A \<Gamma>" by(simp add: \<Gamma>_def)

  have "f ((u, v), x, y) = 0" for u v
  proof(cases "edge \<Gamma> (u, v) (x, y)")
    case False with f show ?thesis by(rule currentD_outside)
  next
    case True
    hence [simp]: "v = x" and ux: "edge \<Delta> u x" by(auto simp add: \<Gamma>_def)
    have "(x, y) \<in> RF S"
    proof
      fix q b
      assume q: "path \<Gamma> (x, y) q b" and b: "b \<in> B \<Gamma>"
      define xy where "xy = (x, y)"
      from q have "path \<Delta> (snd xy) (map snd q) (snd b)" unfolding xy_def[symmetric]
        by(induction)(auto intro: rtrancl_path.intros simp add: \<Gamma>_def)
      with b have "path \<Delta> y (map snd q) (sink \<Delta>)" by(auto simp add: xy_def \<Gamma>_def)
      from roofedD[OF y[unfolded cut_of_sep_def] this] have "\<exists>z\<in>set (y # map snd q). z \<in> ?S"
        by(auto intro: roofed_greaterI simp add: cut_of_sep_def)
      from split_list_last_prop[OF this] obtain xs z ys where decomp: "y # map snd q = xs @ z # ys"
        and z: "z \<in> ?S" and last: "\<And>z. z \<in> set ys \<Longrightarrow> z \<notin> ?S" by auto
      from decomp obtain x' xs' z'' ys' where decomp': "(x', y) # q = xs' @ (z'', z) # ys'"
        and "xs = map snd xs'" and ys: "ys = map snd ys'" and x': "xs' = [] \<Longrightarrow> x' = x"
        by(fastforce simp add: Cons_eq_append_conv map_eq_append_conv)
      from cut z have z_sink: "z \<noteq> sink \<Delta>" by cases(auto)
      then have "ys' \<noteq> []" using rtrancl_path_last[OF q] decomp' b x' q
        by(auto simp add: Cons_eq_append_conv \<Gamma>_def elim: rtrancl_path.cases)
      then obtain w z''' ys'' where ys': "ys' = (w, z''') # ys''" by(auto simp add: neq_Nil_conv)
      from q[THEN rtrancl_path_nth, of "length xs'"] decomp' ys' x' have "edge \<Gamma> (z'', z) (w, z''')"
        by(auto simp add: Cons_eq_append_conv nth_append)
      hence w: "w = z" and zz''': "edge \<Delta> z z'''" by(auto simp add: \<Gamma>_def)
      from ys' ys last[of z'''] have "z''' \<notin> ?S" by simp
      with zz''' z have "(z, z''') \<in> S" by(rule orthogonal_leave_RF)
      moreover have "(z, z''') \<in> set q" using decomp' ys' w by(auto simp add: Cons_eq_append_conv)
      ultimately show "(\<exists>z\<in>set q. z \<in> S) \<or> (x, y) \<in> S" by blast
    qed
    moreover
    have "(u, x) \<notin> RF\<^sup>\<circ> S"
    proof
      assume "(u, x) \<in> RF\<^sup>\<circ> S"
      hence ux_RF: "(u, x) \<in> RF (\<E> S)" and ux_\<E>: "(u, x) \<notin> \<E> S"
        unfolding RF_essential by(simp_all add: roofed_circ_def)

      have "x \<noteq> sink \<Delta>" using p xy by cases(auto simp add: sink_out)
      with p have nNil: "p \<noteq> []" by(auto elim: rtrancl_path.cases)
      with p have "edge \<Delta> x (hd p)" by cases auto
      with ux have "edge \<Gamma> (u, x) (x, hd p)" by(simp add: \<Gamma>_def)
      moreover
      from p nNil have "path \<Gamma> (x, hd p) (zip p (tl p)) (last (x # butlast p), sink \<Delta>)" (is "path _ ?x ?p ?t")
      proof(induction)
        case (step x y p z)
        then show ?case
          by(cases p)(auto elim: rtrancl_path.cases intro: rtrancl_path.intros simp add: \<Gamma>_def)
      qed simp
      ultimately have p': "path \<Gamma> (u, x) (?x # ?p) ?t" ..

      have "(?x # ?p) ! (length p - 1) = ?t" using rtrancl_path_last[OF p] p nNil
        apply(auto split: if_split_asm simp add: nth_Cons butlast_conv_take take_Suc_conv_app_nth not_le split: nat.split elim: rtrancl_path.cases)
        apply(simp add: last_conv_nth nth_tl)
        done
      moreover have "length p - 1 < length (?x # ?p)" by simp
      ultimately have t: "?t \<in> B \<Gamma>" using rtrancl_path_nth[OF p', of "length p - 1"]
        by(cases p)(simp_all add: \<Gamma>_def split: if_split_asm)
      from roofedD[OF ux_RF p' t] ux_\<E> consider (X) "(x, hd p) \<in> \<E> S"
        | (z) z z' where "(z, z') \<in> set (zip p (tl p))" "(z, z') \<in> \<E> S" by auto
      thus False
      proof cases
        case X with x' show False by(auto simp add: cut_of_sep_def intro: rev_image_eqI)
      next
        case (z z)
        with bypass[of z] show False by(auto 4 3 simp add: cut_of_sep_def intro: rev_image_eqI dest!: set_zip_leftD)
      qed
    qed
    ultimately show ?thesis unfolding \<open>v = x\<close> by(rule orthogonal_currentD_in[OF ortho])
  qed
  then have "d_IN f (x, y) = 0" unfolding d_IN_def
    by(simp add: nn_integral_0_iff emeasure_count_space_eq_0)
  with currentD_OUT_IN[OF f A] show "flow_of_current \<Delta> f (x, y) = 0"
    by(simp add: flow_of_current_def max_def)
qed

end

end

subsection \<open>Avoiding antiparallel edges and self-loops\<close>

context antiparallel_edges begin

abbreviation cut' :: "'a vertex set \<Rightarrow> 'a set" where "cut' S \<equiv> Vertex -` S"

lemma cut_cut': "cut \<Delta>'' S \<Longrightarrow> cut \<Delta> (cut' S)"
by(auto simp add: cut.simps)

lemma IN_Edge: "\<^bold>I\<^bold>N\<^bsub>\<Delta>''\<^esub> (Edge x y) = (if edge \<Delta> x y then {Vertex x} else {})"
by(auto simp add: incoming_def)

lemma OUT_Edge: "\<^bold>O\<^bold>U\<^bold>T\<^bsub>\<Delta>''\<^esub> (Edge x y) = (if edge \<Delta> x y then {Vertex y} else {})"
by(auto simp add: outgoing_def)

interpretation \<Delta>'': countable_network \<Delta>'' by(rule \<Delta>''_countable_network)

lemma d_IN_Edge:
  assumes f: "flow \<Delta>'' f"
  shows "d_IN f (Edge x y) = f (Vertex x, Edge x y)"
by(subst d_IN_alt_def[OF \<Delta>''.flowD_outside[OF f], of _ \<Delta>''])(simp_all add: IN_Edge nn_integral_count_space_indicator max_def \<Delta>''.flowD_outside[OF f])

lemma d_OUT_Edge:
  assumes f: "flow \<Delta>'' f"
  shows "d_OUT f (Edge x y) = f (Edge x y, Vertex y)"
by(subst d_OUT_alt_def[OF \<Delta>''.flowD_outside[OF f], of _ \<Delta>''])(simp_all add: OUT_Edge nn_integral_count_space_indicator max_def \<Delta>''.flowD_outside[OF f])

lemma orthogonal_cut':
  assumes ortho: "orthogonal \<Delta>'' f S"
  and f: "flow \<Delta>'' f"
  shows "orthogonal \<Delta> (collect f) (cut' S)"
proof
  show "collect f (x, y) = capacity \<Delta> (x, y)" if edge: "edge \<Delta> x y" and x: "x \<in> cut' S" and y: "y \<notin> cut' S" for x y
  proof(cases "Edge x y \<in> S")
    case True
    from y have "Vertex y \<notin> S" by auto
    from orthogonalD_out[OF ortho _ True this] edge show ?thesis by simp
  next
    case False
    from x have "Vertex x \<in> S" by auto
    from orthogonalD_out[OF ortho _ this False] edge
    have "capacity \<Delta> (x, y) = d_IN f (Edge x y)" by(simp add: d_IN_Edge[OF f])
    also have "\<dots> = d_OUT f (Edge x y)" by(simp add: flowD_KIR[OF f])
    also have "\<dots> = f (Edge x y, Vertex y)" using edge by(simp add: d_OUT_Edge[OF f])
    finally show ?thesis by simp
  qed

  show "collect f (x, y) = 0" if edge: "edge \<Delta> x y" and x: "x \<notin> cut' S" and y: "y \<in> cut' S" for x y
  proof(cases "Edge x y \<in> S")
    case True
    from x have "Vertex x \<notin> S" by auto
    from orthogonalD_in[OF ortho _ this True] edge have "0 = d_IN f (Edge x y)" by(simp add: d_IN_Edge[OF f])
    also have "\<dots> = d_OUT f (Edge x y)" by(simp add: flowD_KIR[OF f])
    also have "\<dots> = f (Edge x y, Vertex y)" using edge by(simp add: d_OUT_Edge[OF f])
    finally show ?thesis by simp
  next
    case False
    from y have "Vertex y \<in> S" by auto
    from orthogonalD_in[OF ortho _ False this] edge show ?thesis by simp
  qed
qed

end

context countable_network begin

lemma countable_web_web_of_network: 
  assumes source_in: "\<And>x. \<not> edge \<Delta> x (source \<Delta>)"
  and sink_out: "\<And>y. \<not> edge \<Delta> (sink \<Delta>) y"
  and undead: "\<And>x y. edge \<Delta> x y \<Longrightarrow> (\<exists>z. edge \<Delta> y z) \<or> (\<exists>z. edge \<Delta> z x)"
  and source_sink: "\<not> edge \<Delta> (source \<Delta>) (sink \<Delta>)"
  and no_loop: "\<And>x. \<not> edge \<Delta> x x"
  shows "countable_web (web_of_network \<Delta>)" (is "countable_web ?\<Gamma>")
proof
  show "\<not> edge ?\<Gamma> y x" if "x \<in> A ?\<Gamma>" for x y using that by(clarsimp simp add: source_in)
  show "\<not> edge ?\<Gamma> x y" if "x \<in> B ?\<Gamma>" for x y using that by(clarsimp simp add: sink_out)
  show "A ?\<Gamma> \<subseteq> \<^bold>V\<^bsub>?\<Gamma>\<^esub>" by(auto 4 3 dest: undead)
  show "A ?\<Gamma> \<inter> B ?\<Gamma> = {}" using source_sink by auto
  show "\<not> edge ?\<Gamma> x x" for x by(auto simp add: no_loop)
  show "weight ?\<Gamma> x = 0" if "x \<notin> \<^bold>V\<^bsub>?\<Gamma>\<^esub>" for x using that undead
    by(cases x)(auto intro!: capacity_outside)
  show "weight ?\<Gamma> x \<noteq> \<top>" for x using capacity_finite[of x] by(cases x) simp
  have "\<^bold>E\<^bsub>?\<Gamma>\<^esub> \<subseteq> \<^bold>E \<times> \<^bold>E" by auto
  thus "countable \<^bold>E\<^bsub>?\<Gamma>\<^esub>" by(rule countable_subset)(simp)
qed


lemma max_flow_min_cut':
  assumes ex_orthogonal_current: " \<exists>f S. web_flow (web_of_network \<Delta>) f \<and> separating (web_of_network \<Delta>) S \<and> orthogonal_current (web_of_network \<Delta>) f S"
  and source_in: "\<And>x. \<not> edge \<Delta> x (source \<Delta>)"
  and sink_out: "\<And>y. \<not> edge \<Delta> (sink \<Delta>) y"
  and undead: "\<And>x y. edge \<Delta> x y \<Longrightarrow> (\<exists>z. edge \<Delta> y z) \<or> (\<exists>z. edge \<Delta> z x)"
  and source_sink: "\<not> edge \<Delta> (source \<Delta>) (sink \<Delta>)"
  and no_loop: "\<And>x. \<not> edge \<Delta> x x"
  and capacity_pos: "\<And>e. e \<in> \<^bold>E \<Longrightarrow> capacity \<Delta> e > 0"
  shows "\<exists>f S. flow \<Delta> f \<and> cut \<Delta> S \<and> orthogonal \<Delta> f S"
proof -
  let ?\<Gamma> = "web_of_network \<Delta>"
  from ex_orthogonal_current obtain f S
    where f: "web_flow (web_of_network \<Delta>) f"
    and S: "separating (web_of_network \<Delta>) S"
    and ortho: "orthogonal_current (web_of_network \<Delta>) f S" by blast+
  let ?f = "flow_of_current \<Delta> f" and ?S = "cut_of_sep \<Delta> S"
  from f have "flow \<Delta> ?f" by(rule flow_flow_of_current)
  moreover have "cut \<Delta> ?S" using S source_neq_sink sink_out by(rule separating_cut)
  moreover have "orthogonal \<Delta> ?f ?S" using f ortho S capacity_pos source_neq_sink sink_out source_sink
    by(rule orthogonal_flow_of_current)
  ultimately show ?thesis by blast
qed

subsection \<open>Eliminating zero edges and incoming edges to @{term source} and outgoing edges of @{term sink}\<close>

definition \<Delta>''' :: "'v network" where "\<Delta>''' =
    \<lparr>edge = \<lambda>x y. edge \<Delta> x y \<and> capacity \<Delta> (x, y) > 0 \<and> y \<noteq> source \<Delta> \<and> x \<noteq> sink \<Delta>,
      capacity = \<lambda>(x, y). if x = sink \<Delta> \<or> y = source \<Delta> then 0 else capacity \<Delta> (x, y),
      source = source \<Delta>,
      sink = sink \<Delta>\<rparr>"

lemma \<Delta>'''_sel [simp]:
  "edge \<Delta>''' x y \<longleftrightarrow> edge \<Delta> x y \<and> capacity \<Delta> (x, y) > 0 \<and> y \<noteq> source \<Delta> \<and> x \<noteq> sink \<Delta>"
  "capacity \<Delta>''' (x, y) = (if x = sink \<Delta> \<or> y = source \<Delta> then 0 else capacity \<Delta> (x, y))"
  "source \<Delta>''' = source \<Delta>"
  "sink \<Delta>''' = sink \<Delta>"
  for x y by(simp_all add: \<Delta>'''_def)

lemma \<Delta>'''_countable_network: "countable_network \<Delta>'''"
proof(unfold_locales)
  have "\<^bold>E\<^bsub>\<Delta>'''\<^esub> \<subseteq> \<^bold>E" by auto
  then show "countable \<^bold>E\<^bsub>\<Delta>'''\<^esub>" by(rule countable_subset) simp
  show "capacity \<Delta>''' e = 0" if "e \<notin> \<^bold>E\<^bsub>\<Delta>'''\<^esub>" for e
    using capacity_outside[of e] that by(auto split: if_split_asm intro: ccontr)
qed(auto simp add: split: if_split_asm)

lemma flow_\<Delta>''':
  assumes f: "flow \<Delta>''' f" and cut: "cut \<Delta>''' S" and ortho: "orthogonal \<Delta>''' f S"
    shows "flow \<Delta> f" "cut \<Delta> S" "orthogonal \<Delta> f S"
proof -
  interpret \<Delta>''': countable_network \<Delta>''' by(rule \<Delta>'''_countable_network)
  show "flow \<Delta> f"
  proof
    show "f e \<le> capacity \<Delta> e" for e using flowD_capacity[OF f, of e]
      by(cases e)(simp split: if_split_asm)
    show "KIR f x" if "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>" for x using flowD_KIR[OF f, of x] that by simp
  qed
  show "cut \<Delta> S" using cut by(simp add: cut.simps)
  show "orthogonal \<Delta> f S"
  proof
    show "f (x, y) = capacity \<Delta> (x, y)" if edge: "edge \<Delta> x y" and x: "x \<in> S" and y: "y \<notin> S" for x y
    proof(cases "edge \<Delta>''' x y")
      case True
      with orthogonalD_out[OF ortho this x y] show ?thesis by simp
    next
      case False
      from cut y x have xy: "y \<noteq> source \<Delta> \<and> x \<noteq> sink \<Delta>" by(cases) auto
      with xy edge False have "capacity \<Delta> (x, y) = 0" by simp
      with \<Delta>'''.flowD_outside[OF f, of "(x, y)"] False show ?thesis by simp
    qed

    show "f (x, y) = 0" if edge: "edge \<Delta> x y" and x: "x \<notin> S" and y: "y \<in> S" for x y
      using orthogonalD_in[OF ortho _ x y] \<Delta>'''.flowD_outside[OF f, of "(x, y)"]
      by(cases "edge \<Delta>''' x y")simp_all
  qed
qed

end

end