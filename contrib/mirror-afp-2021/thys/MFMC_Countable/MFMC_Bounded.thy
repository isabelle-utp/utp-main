(* Author: Andreas Lochbihler, Digital Asset *)

section \<open>The max-flow min-cut theorem in bounded networks\<close>

subsection \<open>Linkages in unhindered bipartite webs\<close>

theory MFMC_Bounded imports
  Matrix_For_Marginals
  MFMC_Reduction
begin

context countable_bipartite_web begin

lemma countable_A [simp]: "countable (A \<Gamma>)"
  using A_vertex countable_V by(blast intro: countable_subset)

lemma unhindered_criterion [rule_format]:
  assumes "\<not> hindered \<Gamma>"
  shows "\<forall>X \<subseteq> A \<Gamma>. finite X \<longrightarrow> (\<Sum>\<^sup>+ x\<in>X. weight \<Gamma> x) \<le> (\<Sum>\<^sup>+ y\<in>\<^bold>E `` X. weight \<Gamma> y)"
  using assms
proof(rule contrapos_np)
  assume "\<not> ?thesis"
  then obtain X where "X \<in> {X. X \<subseteq> A \<Gamma> \<and> finite X \<and> (\<Sum>\<^sup>+ y\<in>\<^bold>E `` X. weight \<Gamma> y) < (\<Sum>\<^sup>+ x\<in>X. weight \<Gamma> x)}" (is "_ \<in> Collect ?P") 
    by(auto simp add: not_le)
  from wf_eq_minimal[THEN iffD1, OF wf_finite_psubset, rule_format, OF this, simplified]
  obtain X where X_A: "X \<subseteq> A \<Gamma>" and fin_X [simp]: "finite X"
    and less: "(\<Sum>\<^sup>+ y\<in>\<^bold>E `` X. weight \<Gamma> y) < (\<Sum>\<^sup>+ x\<in>X. weight \<Gamma> x)"
    and minimal: "\<And>X'. X' \<subset> X \<Longrightarrow> (\<Sum>\<^sup>+ x\<in>X'. weight \<Gamma> x) \<le> (\<Sum>\<^sup>+ y\<in>\<^bold>E `` X'. weight \<Gamma> y)"
    by(clarsimp simp add: not_less)(meson finite_subset order_trans psubset_imp_subset)
  have nonempty: "X \<noteq> {}" using less by auto
  then obtain xx where xx: "xx \<in> X" by auto
  define f where
    "f x = (if x = xx then (\<Sum>\<^sup>+ y\<in>\<^bold>E `` X. weight \<Gamma> y) - (\<Sum>\<^sup>+ x\<in>X - {xx}. weight \<Gamma> x) else if x \<in> X then weight \<Gamma> x else 0)" for x
  define g where
    "g y = (if y \<in> \<^bold>E `` X then weight \<Gamma> y else 0)" for y
  define E' where "E' \<equiv> \<^bold>E \<inter> X \<times> UNIV"
  have Xxx: "X - {xx} \<subset> X" using xx by blast
  have E [simp]: "E' `` X' = \<^bold>E `` X'" if "X' \<subseteq> X" for X' using that by(auto simp add: E'_def)
  have in_E': "(x, y) \<in> E' \<longleftrightarrow> x \<in> X \<and> (x, y) \<in> \<^bold>E" for x y by(auto simp add: E'_def)

  have "(\<Sum>\<^sup>+ x\<in>X. f x) = (\<Sum>\<^sup>+ x\<in>X - {xx}. f x) + (\<Sum>\<^sup>+ x\<in>{xx}. f x)" using xx
    by(auto simp add: nn_integral_count_space_indicator nn_integral_add[symmetric] simp del: nn_integral_indicator_singleton intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = (\<Sum>\<^sup>+ x\<in>X - {xx}. weight \<Gamma> x) + ((\<Sum>\<^sup>+ y\<in>\<^bold>E `` X. weight \<Gamma> y) - (\<Sum>\<^sup>+ x\<in>X - {xx}. weight \<Gamma> x))"
    by(rule arg_cong2[where f="(+)"])(auto simp add: f_def xx nn_integral_count_space_indicator intro!: nn_integral_cong)
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>\<^bold>E `` X. g y)" using minimal[OF Xxx] xx 
    by(subst add_diff_eq_iff_ennreal[THEN iffD2])(fastforce simp add: g_def[abs_def] nn_integral_count_space_indicator intro!: nn_integral_cong intro: nn_integral_mono elim: order_trans split: split_indicator)+
  finally have sum_eq: "(\<Sum>\<^sup>+ x\<in>X. f x) = (\<Sum>\<^sup>+ y\<in>\<^bold>E `` X. g y)" .

  have "(\<Sum>\<^sup>+ y\<in>\<^bold>E `` X. weight \<Gamma> y) = (\<Sum>\<^sup>+ y\<in>\<^bold>E `` X. g y)"
    by(auto simp add: nn_integral_count_space_indicator g_def intro!: nn_integral_cong)
  then have fin: "\<dots> \<noteq> \<top>" using less by auto

  have fin2: "(\<Sum>\<^sup>+ x\<in>X'. weight \<Gamma> x) \<noteq> \<top>" if "X' \<subset> X" for X'
  proof -
    have "(\<Sum>\<^sup>+ x\<in>\<^bold>E `` X'. weight \<Gamma> x) \<le> (\<Sum>\<^sup>+ x\<in>\<^bold>E `` X. weight \<Gamma> x)" using that 
      by(auto 4 3 simp add: nn_integral_count_space_indicator intro!: nn_integral_mono split: split_indicator split_indicator_asm)
    then show ?thesis using minimal[OF that] less by(auto simp add: top_unique)
  qed

  have "f xx = (\<Sum>\<^sup>+ y\<in>\<^bold>E `` X. weight \<Gamma> y) - (\<Sum>\<^sup>+ x\<in>X - {xx}. weight \<Gamma> x)" by (simp add: f_def)
  also have "\<dots> < (\<Sum>\<^sup>+ x\<in>X. weight \<Gamma> x) - (\<Sum>\<^sup>+ x\<in>X - {xx}. weight \<Gamma> x)" using less fin2[OF Xxx] minimal[OF Xxx]
    by(subst minus_less_iff_ennreal)(fastforce simp add: less_top[symmetric] nn_integral_count_space_indicator diff_add_self_ennreal intro: nn_integral_mono elim: order_trans split: split_indicator)+
  also have "\<dots> = (\<Sum>\<^sup>+ x\<in>{xx}. weight \<Gamma> x)" using fin2[OF Xxx] xx 
    apply(simp add: nn_integral_count_space_indicator del: nn_integral_indicator_singleton)
    apply(subst nn_integral_diff[symmetric])
    apply(auto simp add: AE_count_space split: split_indicator simp del: nn_integral_indicator_singleton intro!: nn_integral_cong)
    done
  also have "\<dots> = weight \<Gamma> xx" by(simp add: nn_integral_count_space_indicator)
  finally have fxx: "f xx < weight \<Gamma> xx" .

  have le: "(\<Sum>\<^sup>+ x\<in>X'. f x) \<le> (\<Sum>\<^sup>+ y\<in>\<^bold>E `` X'. g y)" if "X' \<subseteq> X" for X'
  proof(cases "X' = X")
    case True
    then show ?thesis using sum_eq by simp
  next
    case False
    hence X': "X' \<subset> X" using that by blast
    have "(\<Sum>\<^sup>+ x\<in>X'. f x) = (\<Sum>\<^sup>+ x\<in>X' - {xx}. f x) + (\<Sum>\<^sup>+ x\<in>{xx}. f x * indicator X' xx)"
      by(auto simp add: nn_integral_count_space_indicator nn_integral_add[symmetric] simp del: nn_integral_indicator_singleton intro!: nn_integral_cong split: split_indicator)
    also have "\<dots> \<le> (\<Sum>\<^sup>+ x\<in>X' - {xx}. f x) + (\<Sum>\<^sup>+ x\<in>{xx}. weight \<Gamma> x * indicator X' xx)" using fxx
      by(intro add_mono)(auto split: split_indicator simp add: nn_integral_count_space_indicator)
    also have "\<dots> = (\<Sum>\<^sup>+ x\<in>X'. weight \<Gamma> x)" using xx that
      by(auto simp add: nn_integral_count_space_indicator nn_integral_add[symmetric] f_def simp del: nn_integral_indicator_singleton intro!: nn_integral_cong split: split_indicator)
    also have "\<dots> \<le> (\<Sum>\<^sup>+ y\<in>\<^bold>E `` X'. weight \<Gamma> y)" by(rule minimal[OF X'])
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>\<^bold>E `` X'. g y)" using that 
      by(auto 4 3 intro!: nn_integral_cong simp add: g_def Image_iff)
    finally show ?thesis .
  qed
  
  have "countable X" using X_A A_vertex countable_V by(blast intro: countable_subset)
  moreover have "\<^bold>E `` X \<subseteq> \<^bold>V" by(auto simp add: vertex_def)
  with countable_V have "countable (\<^bold>E `` X)" by(blast intro: countable_subset)
  moreover have "E' \<subseteq> X \<times> \<^bold>E `` X" by(auto simp add: E'_def)
  ultimately obtain h' where h'_dom: "\<And>x y. 0 < h' x y \<Longrightarrow> (x, y) \<in> E'"
    and h'_fin: "\<And>x y. h' x y \<noteq> \<top>"
    and h'_f: "\<And>x. x \<in> X \<Longrightarrow> (\<Sum>\<^sup>+ y\<in>E' `` X. h' x y) = f x"
    and h'_g: "\<And>y. y \<in> E' `` X \<Longrightarrow> (\<Sum>\<^sup>+ x\<in>X. h' x y) = g y"
    using bounded_matrix_for_marginals_ennreal[where f=f and g=g and A=X and B="E' `` X" and R=E' and thesis=thesis] sum_eq fin le
    by(auto)

  have h'_outside: "(x, y) \<notin> E' \<Longrightarrow> h' x y = 0" for x y using h'_dom[of x y] not_gr_zero by(fastforce)

  define h where "h = (\<lambda>(x, y). if x \<in> X \<and> edge \<Gamma> x y then h' x y else 0)"
  have h_OUT: "d_OUT h x = (if x \<in> X then f x else 0)" for x
    by(auto 4 3 simp add: h_def d_OUT_def h'_f[symmetric] E'_def nn_integral_count_space_indicator intro!: nn_integral_cong intro: h'_outside split: split_indicator)
  have h_IN: "d_IN h y = (if y \<in> \<^bold>E `` X then weight \<Gamma> y else 0)" for y using h'_g[of y, symmetric]
    by(auto 4 3 simp add: h_def d_IN_def g_def nn_integral_count_space_indicator nn_integral_0_iff_AE  in_E' intro!: nn_integral_cong intro: h'_outside split: split_indicator split_indicator_asm)

  have h: "current \<Gamma> h"
  proof
    show "d_OUT h x \<le> weight \<Gamma> x" for x using fxx by(auto simp add: h_OUT f_def)
    show "d_IN h y \<le> weight \<Gamma> y" for y by(simp add: h_IN)
    show "h e = 0" if "e \<notin> \<^bold>E" for e using that by(cases e)(auto simp add: h_def)
  qed

  have "separating \<Gamma> (TER h)"
  proof
    fix x y p
    assume x: "x \<in> A \<Gamma>" and y: "y \<in> B \<Gamma>" and p: "path \<Gamma> x p y"
    then obtain [simp]: "p = [y]" and xy: "(x, y) \<in> \<^bold>E" using disjoint 
      by -(erule rtrancl_path.cases; auto dest: bipartite_E)+
    show "(\<exists>z\<in>set p. z \<in> TER h) \<or> x \<in> TER h"
    proof(rule disjCI)
      assume "x \<notin> TER h"
      hence "x \<in> X" using x by(auto simp add: SAT.simps SINK.simps h_OUT split: if_split_asm)
      hence "y \<in> TER h" using xy currentD_OUT[OF h y] by(auto simp add: SAT.simps h_IN SINK.simps)
      thus "\<exists>z\<in>set p. z \<in> TER h" by simp
    qed
  qed
  then have w: "wave \<Gamma> h" using h ..

  have "xx \<in> A \<Gamma>" using xx X_A by blast
  moreover have "xx \<notin> \<E> (TER h)"
  proof
    assume "xx \<in> \<E> (TER h)"
    then obtain p y where y: "y \<in> B \<Gamma>" and p: "path \<Gamma> xx p y"
      and bypass: "\<And>z. \<lbrakk> xx \<noteq> y; z \<in> set p \<rbrakk> \<Longrightarrow> z = xx \<or> z \<notin> TER h"
      by(rule \<E>_E) auto
    from p obtain [simp]: "p = [y]" and xy: "edge \<Gamma> xx y" and neq: "xx \<noteq> y" using disjoint X_A xx y
      by -(erule rtrancl_path.cases; auto dest: bipartite_E)+
    from neq bypass[of y] have "y \<notin> TER h" by simp
    moreover from xy xx currentD_OUT[OF h y] have "y \<in> TER h" 
      by(auto simp add: SAT.simps h_IN SINK.simps)
    ultimately show False by contradiction
  qed
  moreover have "d_OUT h xx < weight \<Gamma> xx" using fxx xx by(simp add: h_OUT)
  ultimately have "hindrance \<Gamma> h" ..
  then show "hindered \<Gamma>" using h w ..
qed

end

lemma nn_integral_count_space_top_approx:
  fixes f :: "nat => ennreal" and b :: ennreal
  assumes "nn_integral (count_space UNIV) f = top"
  and "b < top"
  obtains n where "b < sum f {..<n}"
  using assms unfolding nn_integral_count_space_nat suminf_eq_SUP SUP_eq_top_iff by(auto)

lemma One_le_of_nat_ennreal: "(1 :: ennreal) \<le> of_nat x \<longleftrightarrow> 1 \<le> x"
  by (metis of_nat_le_iff of_nat_1)

locale bounded_countable_bipartite_web = countable_bipartite_web \<Gamma>
  for \<Gamma> :: "('v, 'more) web_scheme" (structure)
  +
  assumes bounded_B: "x \<in> A \<Gamma> \<Longrightarrow> (\<Sum>\<^sup>+ y \<in> \<^bold>E `` {x}. weight \<Gamma> y) < \<top>"
begin

theorem unhindered_linkable_bounded:
  assumes "\<not> hindered \<Gamma>"
  shows "linkable \<Gamma>"
proof(cases "A \<Gamma> = {}")
  case True
  hence "linkage \<Gamma> (\<lambda>_. 0)" by(auto simp add: linkage.simps)
  moreover have "web_flow \<Gamma> (\<lambda>_. 0)" by(auto simp add: web_flow.simps)
  ultimately show ?thesis by blast 
next
  case nonempty: False
  define A_n :: "nat \<Rightarrow> 'v set" where "A_n n = from_nat_into (A \<Gamma>) ` {..n}" for n
  have fin_A_n [simp]: "finite (A_n n)" for n by(simp add: A_n_def)
  have A_n_A: "A_n n \<subseteq> A \<Gamma>" for n by(auto simp add: A_n_def from_nat_into[OF nonempty])

  have countable2: "countable (\<^bold>E `` A_n n)" for n using countable_V
    by(rule countable_subset[rotated])(auto simp add: vertex_def)

  have "\<exists>Y2. \<forall>n. \<forall>X \<subseteq> A_n n. Y2 n X \<subseteq> \<^bold>E `` X \<and> (\<Sum>\<^sup>+ x\<in>X. weight \<Gamma> x) \<le> (\<Sum>\<^sup>+ y\<in>Y2 n X. weight \<Gamma> y) \<and> (\<Sum>\<^sup>+ y\<in>Y2 n X. weight \<Gamma> y) \<noteq> \<top>"
  proof(rule choice strip ex_simps(6)[THEN iffD2])+
    fix n X
    assume X: "X \<subseteq> A_n n"
    then have [simp]: "finite X" by(rule finite_subset) simp
    have X_count: "countable (\<^bold>E `` X)" using countable2
      by(rule countable_subset[rotated])(rule Image_mono[OF order_refl X])

    show "\<exists>Y. Y \<subseteq> \<^bold>E `` X \<and> (\<Sum>\<^sup>+ x\<in>X. weight \<Gamma> x) \<le> (\<Sum>\<^sup>+ y\<in>Y. weight \<Gamma> y) \<and> (\<Sum>\<^sup>+ y\<in>Y. weight \<Gamma> y) \<noteq> \<top>" (is "Ex ?P")
    proof(cases "(\<Sum>\<^sup>+ y\<in>\<^bold>E `` X. weight \<Gamma> y) = \<top>")
      case True
      define Y' where "Y' = to_nat_on (\<^bold>E `` X) ` (\<^bold>E `` X)"
      have inf: "infinite (\<^bold>E `` X)" using True
        by(intro notI)(auto simp add: nn_integral_count_space_finite)
      then have Y': "Y' = UNIV" using X_count by(auto simp add: Y'_def intro!: image_to_nat_on)
      have "(\<Sum>\<^sup>+ y\<in>\<^bold>E `` X. weight \<Gamma> y) = (\<Sum>\<^sup>+ y\<in>from_nat_into (\<^bold>E `` X) ` Y'. weight \<Gamma> y * indicator (\<^bold>E `` X) y)"
        using X_count
        by(auto simp add: nn_integral_count_space_indicator Y'_def image_image intro!: nn_integral_cong from_nat_into_to_nat_on[symmetric] rev_image_eqI split: split_indicator)
      also have "\<dots> = (\<Sum>\<^sup>+ y. weight \<Gamma> (from_nat_into (\<^bold>E `` X) y) * indicator (\<^bold>E `` X) (from_nat_into (\<^bold>E `` X) y))"
        using X_count inf by(subst nn_integral_count_space_reindex)(auto simp add: inj_on_def Y')
      finally have "\<dots> = \<top>" using True by simp
      from nn_integral_count_space_top_approx[OF this, of "sum (weight \<Gamma>) X"]
      obtain yy where yy: "sum (weight \<Gamma>) X < (\<Sum> y<yy. weight \<Gamma> (from_nat_into (\<^bold>E `` X) y) * indicator (\<^bold>E `` X) (from_nat_into (\<^bold>E `` X) y))"
        by(auto simp add: less_top[symmetric])
      define Y where "Y = from_nat_into (\<^bold>E `` X) ` {..<yy} \<inter> \<^bold>E `` X"
      have [simp]: "finite Y" by(simp add: Y_def)
      have "(\<Sum>\<^sup>+ x\<in>X. weight \<Gamma> x) = sum (weight \<Gamma>) X" by(simp add: nn_integral_count_space_finite)
      also have "\<dots> \<le> (\<Sum> y<yy. weight \<Gamma> (from_nat_into (\<^bold>E `` X) y) * indicator (\<^bold>E `` X) (from_nat_into (\<^bold>E `` X) y))"
        using yy by simp
      also have "\<dots> = (\<Sum> y \<in> from_nat_into (\<^bold>E `` X) ` {..<yy}. weight \<Gamma> y * indicator (\<^bold>E `` X) y)"
        using X_count inf by(subst sum.reindex)(auto simp add: inj_on_def)
      also have "\<dots> = (\<Sum> y \<in> Y. weight \<Gamma> y)" by(auto intro!: sum.cong simp add: Y_def)
      also have "\<dots> = (\<Sum>\<^sup>+ y\<in>Y. weight \<Gamma> y)" by(simp add: nn_integral_count_space_finite)
      also have "Y \<subseteq> \<^bold>E `` X" by(simp add: Y_def)
      moreover have "(\<Sum>\<^sup>+ y\<in>Y. weight \<Gamma> y) \<noteq> \<top>" by(simp add: nn_integral_count_space_finite)
      ultimately show ?thesis by blast
    next
      case False
      with unhindered_criterion[OF assms, of X] X A_n_A[of n] have "?P (\<^bold>E `` X)" by auto
      then show ?thesis ..
    qed
  qed
  then obtain Y2
    where Y2_A: "Y2 n X \<subseteq> \<^bold>E `` X"
    and le: "(\<Sum>\<^sup>+ x\<in>X. weight \<Gamma> x) \<le> (\<Sum>\<^sup>+ y\<in>Y2 n X. weight \<Gamma> y)"
    and finY2: "(\<Sum>\<^sup>+ y\<in>Y2 n X. weight \<Gamma> y) \<noteq> \<top>" if "X \<subseteq> A_n n" for n X by iprover
  define Y where "Y n = (\<Union> X \<in> Pow (A_n n). Y2 n X)" for n
  define s where "s n = (\<Sum>\<^sup>+ y\<in>Y n. weight \<Gamma> y)" for n
  have Y_vertex: "Y n \<subseteq> \<^bold>V" for n by(auto 4 3 simp add: Y_def vertex_def dest!: Y2_A[of _ n])
  have Y_B: "Y n \<subseteq> B \<Gamma>" for n unfolding Y_def by(auto dest!: Y2_A[of _ n] dest: bipartite_E)

  have s_top [simp]: "s n \<noteq> \<top>" for n
  proof -
    have "\<lbrakk>x \<in> Y2 n X; X \<subseteq> A_n n\<rbrakk> \<Longrightarrow> Suc 0 \<le> card {X. X \<subseteq> A_n n \<and> x \<in> Y2 n X}" for x X
      by(subst card_le_Suc_iff)(auto intro!: exI[where x=X] exI[where x="{X. X \<subseteq> A_n n \<and> x \<in> Y2 n X} - {X}"])
    then have "(\<Sum>\<^sup>+ y\<in>Y n. weight \<Gamma> y) \<le> (\<Sum>\<^sup>+ y\<in>Y n. \<Sum> X\<in>Pow (A_n n). weight \<Gamma> y * indicator (Y2 n X) y)"
      by(intro nn_integral_mono)(auto simp add: Y_def One_le_of_nat_ennreal intro!: mult_right_mono[of "1 :: ennreal", simplified])
    also have "\<dots> = (\<Sum> X\<in>Pow (A_n n). \<Sum>\<^sup>+ y\<in>Y n. weight \<Gamma> y * indicator (Y2 n X) y)"
      by(subst nn_integral_sum) auto
    also have "\<dots> = (\<Sum> X\<in>Pow (A_n n). \<Sum>\<^sup>+ y\<in>Y2 n X. weight \<Gamma> y)"
      by(auto intro!: sum.cong nn_integral_cong simp add: nn_integral_count_space_indicator Y_def split: split_indicator)
    also have "\<dots> < \<top>" by(simp add: less_top[symmetric] finY2)
    finally show ?thesis by(simp add: less_top s_def)
  qed

  define f :: "nat \<Rightarrow> 'v option \<Rightarrow> real"
    where "f n xo = (case xo of Some x \<Rightarrow> if x \<in> A_n n then enn2real (weight \<Gamma> x) else 0 
                    | None \<Rightarrow> enn2real (s n - sum (weight \<Gamma>) (A_n n)))" for n xo
  define g :: "nat \<Rightarrow> 'v \<Rightarrow> real"
    where "g n y = enn2real (weight \<Gamma> y * indicator (Y n) y)" for n y
  define R :: "nat \<Rightarrow> ('v option \<times> 'v) set"
    where "R n = map_prod Some id ` (\<^bold>E \<inter> A_n n \<times> Y n) \<union> {None} \<times> Y n" for n
  define A_n' where "A_n' n = Some ` A_n n \<union> {None}" for n

  have f_simps:
    "f n (Some x) = (if x \<in> A_n n then enn2real (weight \<Gamma> x) else 0)"
    "f n None = enn2real (s n - sum (weight \<Gamma>) (A_n n))"
    for n x by(simp_all add: f_def)
  
  have g_s: "(\<Sum>\<^sup>+ y\<in>Y n. g n y) = s n" for n
    by(auto simp add: s_def g_def ennreal_enn2real_if intro!: nn_integral_cong)

  have "(\<Sum>\<^sup>+ x\<in>A_n' n. f n x) = (\<Sum>\<^sup>+ x\<in>Some`A_n n. weight \<Gamma> (the x)) + (\<Sum>\<^sup>+ x\<in>{None}. f n x)" for n
    by(auto simp add: nn_integral_count_space_indicator nn_integral_add[symmetric] f_simps A_n'_def ennreal_enn2real_if simp del: nn_integral_indicator_singleton intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> n = sum (weight \<Gamma>) (A_n n) + (s n - sum (weight \<Gamma>) (A_n n))" for n
    by(subst nn_integral_count_space_reindex)(auto simp add: nn_integral_count_space_finite f_simps ennreal_enn2real_if)
  also have "\<dots> n = s n" for n using le[OF order_refl, of n]
    by(simp add: s_def nn_integral_count_space_finite)(auto elim!: order_trans simp add: nn_integral_count_space_indicator Y_def intro!: nn_integral_mono split: split_indicator)
  finally have sum_eq: "(\<Sum>\<^sup>+ x\<in>A_n' n. f n x) = (\<Sum>\<^sup>+ y\<in>Y n. g n y)" for n using g_s by simp

  have "\<exists>h'. \<forall>n. (\<forall>x y. (x, y) \<notin> R n \<longrightarrow> h' n x y = 0) \<and> (\<forall>x y. h' n x y \<noteq> \<top>) \<and> (\<forall>x\<in>A_n' n. (\<Sum>\<^sup>+ y\<in>Y n. h' n x y) = f n x) \<and> (\<forall>y\<in>Y n. (\<Sum>\<^sup>+ x\<in>A_n' n. h' n x y) = g n y)" 
    (is "Ex (\<lambda>h'. \<forall>n. ?Q n (h' n))")
  proof(rule choice allI)+
    fix n
    note sum_eq
    moreover have "(\<Sum>\<^sup>+ y\<in>Y n. g n y) \<noteq> \<top>" using g_s by simp
    moreover have le_fg: "(\<Sum>\<^sup>+ x\<in>X. f n x) \<le> (\<Sum>\<^sup>+ y\<in>R n `` X. g n y)" if "X \<subseteq> A_n' n" for X
    proof(cases "None \<in> X")
      case True
      have "(\<Sum>\<^sup>+ x\<in>X. f n x) \<le> (\<Sum>\<^sup>+ x\<in>A_n' n. f n x)" using that
        by(auto simp add: nn_integral_count_space_indicator intro!: nn_integral_mono split: split_indicator)
      also have "\<dots> = (\<Sum>\<^sup>+ y\<in>Y n. g n y)" by(simp add: sum_eq)
      also have "R n `` X = Y n" using True by(auto simp add: R_def)
      ultimately show ?thesis by simp
    next
      case False
      then have *: "Some ` (the ` X) = X"
        by(auto simp add: image_image)(metis (no_types, lifting) image_iff notin_range_Some option.sel option.collapse)+
      from False that have X: "the ` X \<subseteq> A_n n" by(auto simp add: A_n'_def)
      from * have "(\<Sum>\<^sup>+ x\<in>X. f n x) = (\<Sum>\<^sup>+ x\<in>Some ` (the ` X). f n x)" by simp
      also have "\<dots> = (\<Sum>\<^sup>+ x\<in>the ` X. f n (Some x))" by(rule nn_integral_count_space_reindex) simp
      also have "\<dots> = (\<Sum>\<^sup>+ x\<in>the ` X. weight \<Gamma> x)" using that False
        by(auto 4  3intro!: nn_integral_cong simp add: f_simps A_n'_def ennreal_enn2real_if)
      also have "\<dots> \<le> (\<Sum>\<^sup>+ y\<in>Y2 n (the ` X). weight \<Gamma> y)" using False that 
        by(intro le)(auto simp add: A_n'_def)
      also have "\<dots> \<le> (\<Sum>\<^sup>+ y\<in>R n `` X. weight \<Gamma> y)" using False Y2_A[of "the ` X" n] X
        by(auto simp add: A_n'_def nn_integral_count_space_indicator R_def Image_iff Y_def intro: rev_image_eqI intro!: nn_integral_mono split: split_indicator)
          (drule (1) subsetD; clarify; drule (1) bspec; auto 4 3 intro: rev_image_eqI)
      also have "\<dots> = (\<Sum>\<^sup>+ y\<in>R n `` X. g n y)"
        by(auto intro!: nn_integral_cong simp add: R_def g_def ennreal_enn2real_if)
      finally show ?thesis .
    qed
    moreover have "countable (A_n' n)" by(simp add: A_n'_def countable_finite)
    moreover have "countable (Y2 n X)" if "X \<subseteq> A_n n" for X using Y2_A[OF that]
      by(rule countable_subset)(rule countable_subset[OF _ countable_V]; auto simp add: vertex_def)
    then have "countable (Y n)" unfolding Y_def
      by(intro countable_UN)(simp_all add: countable_finite)
    moreover have "R n \<subseteq> A_n' n \<times> Y n" by(auto simp add: R_def A_n'_def)
    ultimately obtain h' where "\<And>x y. 0 < h' x y \<Longrightarrow> (x, y) \<in> R n" "\<And>x y. h' x y \<noteq> \<top>" 
      "\<And>x. x \<in> A_n' n \<Longrightarrow> (\<Sum>\<^sup>+ y\<in>Y n. h' x y) = (f n x)" "\<And>y. y \<in> Y n \<Longrightarrow> (\<Sum>\<^sup>+ x\<in>A_n' n. h' x y) = g n y"
      by(rule bounded_matrix_for_marginals_ennreal) blast+
    hence "?Q n h'" by(auto)(use not_gr_zero in blast)
    thus "Ex (?Q n)" by blast
  qed
  then obtain h' where dom_h': "\<And>x y. (x, y) \<notin> R n \<Longrightarrow> h' n x y = 0"
    and fin_h' [simp]: "\<And>x y. h' n x y \<noteq> \<top>"
    and h'_f: "\<And>x. x \<in> A_n' n \<Longrightarrow> (\<Sum>\<^sup>+ y\<in>Y n. h' n x y) = f n x"
    and h'_g: "\<And>y. y \<in> Y n \<Longrightarrow> (\<Sum>\<^sup>+ x\<in>A_n' n. h' n x y) = g n y"
    for n by blast
  
  define h :: "nat \<Rightarrow> 'v \<times> 'v \<Rightarrow> real"
    where "h n = (\<lambda>(x, y). if x \<in> A_n n \<and> y \<in> Y n then enn2real (h' n (Some x) y) else 0)" for n
  have h_nonneg: "0 \<le> h n xy" for n xy by(simp add: h_def split_def)
  have h_notB: "h n (x, y) = 0" if "y \<notin> B \<Gamma>" for n x y using Y_B[of n] that by(auto simp add: h_def)
  have h_le_weight2: "h n (x, y) \<le> weight \<Gamma> y" for n x y
  proof(cases "x \<in> A_n n \<and> y \<in> Y n")
    case True
    have "h' n (Some x) y \<le> (\<Sum>\<^sup>+ x\<in>A_n' n. h' n x y)"
      by(rule nn_integral_ge_point)(auto simp add: A_n'_def True)
    also have "\<dots> \<le> weight \<Gamma> y" using h'_g[of y n] True by(simp add: g_def ennreal_enn2real_if)
    finally show ?thesis using True by(simp add: h_def ennreal_enn2real_if)
  qed(auto simp add: h_def)
  have h_OUT: "d_OUT (h n) x = (if x \<in> A_n n then weight \<Gamma> x else 0)" for n x
    using h'_f[of "Some x" n, symmetric]
    by(auto simp add: h_def d_OUT_def A_n'_def f_simps ennreal_enn2real_if nn_integral_count_space_indicator intro!: nn_integral_cong)
  have h_IN: "d_IN (h n) y = (if y \<in> Y n then enn2real (weight \<Gamma> y - h' n None y) else 0)" for n y
  proof(cases "y \<in> Y n")
    case True
    have "d_IN (h n) y = (\<Sum>\<^sup>+ x\<in>Some ` A_n n. h' n x y)"
      by(subst nn_integral_count_space_reindex)
        (auto simp add: d_IN_def h_def nn_integral_count_space_indicator ennreal_enn2real_if R_def intro!: nn_integral_cong dom_h' split: split_indicator)
    also have "\<dots> = (\<Sum>\<^sup>+ x\<in>A_n' n. h' n x y) - (\<Sum>\<^sup>+ x\<in>{None}. h' n x y)"
      apply(simp add: nn_integral_count_space_indicator del: nn_integral_indicator_singleton)
      apply(subst nn_integral_diff[symmetric])
      apply(auto simp add: AE_count_space A_n'_def nn_integral_count_space_indicator split: split_indicator intro!: nn_integral_cong)
      done
    also have "\<dots> = g n y - h' n None y" using h'_g[OF True] by(simp add: nn_integral_count_space_indicator)
    finally show ?thesis using True by(simp add: g_def ennreal_enn2real_if)
  qed(auto simp add: d_IN_def ennreal_enn2real_if nn_integral_0_iff_AE AE_count_space h_def g_def)

  let ?Q = "\<^bold>V \<times> \<^bold>V"

  have "bounded (range (\<lambda>n. h n xy))" if "xy \<in> ?Q" for xy unfolding bounded_def dist_real_def
  proof(rule exI strip|erule imageE|hypsubst)+
    fix n
    obtain x y where [simp]: "xy = (x, y)" by(cases xy)
    have "h n (x, y) \<le> d_OUT (h n) x" unfolding d_OUT_def by(rule nn_integral_ge_point) simp
    also have "\<dots> \<le> weight \<Gamma> x" by(simp add: h_OUT)
    finally show "\<bar>0 - h n xy\<bar> \<le> enn2real (weight \<Gamma> (fst xy))"
      by(simp add: h_nonneg)(metis enn2real_ennreal ennreal_cases ennreal_le_iff weight_finite)
  qed
  moreover have "countable ?Q" using countable_V by(simp)
  ultimately obtain k where k: "strict_mono k" 
    and conv: "\<And>xy. xy \<in> ?Q \<Longrightarrow> convergent (\<lambda>n. h (k n) xy)"
    by(rule convergent_bounded_family) blast+

  have h_outside: "h n xy = 0" if "xy \<notin> ?Q" for xy n using that A_n_A[of n] A_vertex Y_vertex 
    by(auto simp add: h_def split: prod.split)
  have h_outside_AB: "h n (x, y) = 0" if "x \<notin> A \<Gamma> \<or> y \<notin> B \<Gamma>" for n x y 
    using that A_n_A[of n] Y_B[of n] by(auto simp add: h_def)
  have h_outside_E: "h n (x, y) = 0" if "(x, y) \<notin> \<^bold>E" for n x y using that unfolding h_def
    by(clarsimp)(subst dom_h', auto simp add: R_def)

  define H where "H xy = lim (\<lambda>n. h (k n) xy)" for xy
  have H: "(\<lambda>n. h (k n) xy) \<longlonglongrightarrow> H xy" for xy
    using conv[of xy] unfolding H_def by(cases "xy \<in> ?Q")(auto simp add: convergent_LIMSEQ_iff h_outside)
  have H_outside: "H (x, y) = 0" if "x \<notin> A \<Gamma> \<or> y \<notin> B \<Gamma>" for x y
    using that by(simp add: H_def convergent_LIMSEQ_iff h_outside_AB)
  have H': "(\<lambda>n. ennreal (h (k n) xy)) \<longlonglongrightarrow> H xy" for xy
    using H by(rule tendsto_ennrealI)
  have H_def': "H xy = lim (\<lambda>n. ennreal (h (k n) xy))" for xy by (metis H' limI)

  have H_OUT: "d_OUT H x = weight \<Gamma> x" if x: "x \<in> A \<Gamma>" for x
  proof -
    let ?w = "\<lambda>y. if (x, y) \<in> \<^bold>E then weight \<Gamma> y else 0"
    have sum_w: "(\<Sum>\<^sup>+ y. if edge \<Gamma> x y then weight \<Gamma> y else 0) = (\<Sum>\<^sup>+ y \<in> \<^bold>E `` {x}. weight \<Gamma> y)"
      by(simp add: nn_integral_count_space_indicator indicator_def if_distrib cong: if_cong)
    have "(\<lambda>n. d_OUT (h (k n)) x) \<longlonglongrightarrow> d_OUT H x" unfolding d_OUT_def
      by(rule nn_integral_dominated_convergence[where w="?w"])(use bounded_B x in \<open>simp_all add: AE_count_space H h_outside_E h_le_weight2 sum_w\<close>)
    moreover define n_x where "n_x = to_nat_on (A \<Gamma>) x"
    have x': "x \<in> A_n (k n)" if "n \<ge> n_x" for n
      using that seq_suble[OF k, of n] x unfolding A_n_def
      by(intro rev_image_eqI[where x=n_x])(simp_all add: A_n_def n_x_def)
    have "(\<lambda>n. d_OUT (h (k n)) x) \<longlonglongrightarrow> weight \<Gamma> x"
      by(intro tendsto_eventually eventually_sequentiallyI[where c="n_x"])(simp add: h_OUT x')
    ultimately show ?thesis by(rule LIMSEQ_unique)
  qed
  then have "linkage \<Gamma> H" ..
  moreover
  have "web_flow \<Gamma> H" unfolding web_flow_iff
  proof
    show "d_OUT H x \<le> weight \<Gamma> x" for x
      by(cases "x \<in> A \<Gamma>")(simp_all add: H_OUT[unfolded d_OUT_def] H_outside d_OUT_def)

    show "d_IN H y \<le> weight \<Gamma> y" for y
    proof -
      have "d_IN H y = (\<Sum>\<^sup>+ x. liminf (\<lambda>n. ennreal (h (k n) (x, y))))" unfolding d_IN_def H_def'
        by(rule nn_integral_cong convergent_liminf_cl[symmetric] convergentI H')+
      also have "\<dots> \<le> liminf (\<lambda>n. d_IN (h (k n)) y)"
        unfolding d_IN_def by(rule nn_integral_liminf) simp
      also have "\<dots> \<le> liminf (\<lambda>n. weight \<Gamma> y)" unfolding h_IN
        by(rule Liminf_mono)(auto simp add: ennreal_enn2real_if)
      also have "\<dots> = weight \<Gamma> y" by(simp add: Liminf_const)
      finally show "?thesis" .
    qed

    show "ennreal (H e) = 0" if "e \<notin> \<^bold>E" for e
    proof(rule LIMSEQ_unique[OF H'])   
      obtain x y where [simp]: "e = (x, y)" by(cases e)
      have "ennreal (h (k n) (x, y)) = 0" for n
        using dom_h'[of "Some x" y "k n"] that by(auto simp add: h_def R_def enn2real_eq_0_iff elim: meta_mp)
      then show "(\<lambda>n. ennreal (h (k n) e)) \<longlonglongrightarrow> 0" using that 
        by(intro tendsto_eventually eventually_sequentiallyI) simp
    qed
  qed
  ultimately show ?thesis by blast
qed

end

subsection \<open>Glueing the reductions together\<close>

locale bounded_countable_web = countable_web \<Gamma>
  for \<Gamma> :: "('v, 'more) web_scheme" (structure)
  +
  assumes bounded_out: "x \<in> \<^bold>V - B \<Gamma> \<Longrightarrow> (\<Sum>\<^sup>+ y \<in> \<^bold>E `` {x}. weight \<Gamma> y) < \<top>"
begin

lemma bounded_countable_bipartite_web_of: "bounded_countable_bipartite_web (bipartite_web_of \<Gamma>)"
  (is "bounded_countable_bipartite_web ?\<Gamma>")
proof -
  interpret bi: countable_bipartite_web ?\<Gamma> by(rule countable_bipartite_web_of)
  show ?thesis
  proof
    fix x
    assume "x \<in> A ?\<Gamma>"
    then obtain x' where x: "x = Inl x'" and x': "vertex \<Gamma> x'" "x' \<notin> B \<Gamma>" by auto
    have "\<^bold>E\<^bsub>?\<Gamma>\<^esub> `` {x} \<subseteq> Inr ` ({x'} \<union> (\<^bold>E `` {x'}))" using x 
      by(auto simp add: bipartite_web_of_def vertex_def split: sum.split_asm)
    hence "(\<Sum>\<^sup>+ y \<in> \<^bold>E\<^bsub>?\<Gamma>\<^esub> `` {x}. weight ?\<Gamma> y) \<le> (\<Sum>\<^sup>+ y \<in> \<dots>. weight ?\<Gamma> y)"
      by(auto simp add: nn_integral_count_space_indicator intro!: nn_integral_mono split: split_indicator)
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>{x'} \<union> (\<^bold>E `` {x'}). weight (bipartite_web_of \<Gamma>) (Inr y))"
      by(rule nn_integral_count_space_reindex)(auto)
    also have "\<dots> \<le> weight \<Gamma> x' + (\<Sum>\<^sup>+ y \<in> \<^bold>E `` {x'}. weight \<Gamma> y)"
      apply(subst (1 2) nn_integral_count_space_indicator, simp, simp)
      apply(cases "\<not> edge \<Gamma> x' x'")
      apply(subst nn_integral_disjoint_pair)
      apply(auto intro!: nn_integral_mono add_increasing split: split_indicator)
      done
    also have "\<dots> < \<top>" using bounded_out[of x'] x' using weight_finite[of x'] by(simp del: weight_finite add: less_top)
    finally show "(\<Sum>\<^sup>+ y \<in> \<^bold>E\<^bsub>?\<Gamma>\<^esub> `` {x}. weight ?\<Gamma> y) < \<top>"  .
  qed
qed

theorem loose_linkable_bounded:
  assumes "loose \<Gamma>"
  shows "linkable \<Gamma>"
proof -
  interpret bi: bounded_countable_bipartite_web "bipartite_web_of \<Gamma>" by(rule bounded_countable_bipartite_web_of)
  have "\<not> hindered (bipartite_web_of \<Gamma>)" using assms by(rule unhindered_bipartite_web_of)
  then have "linkable (bipartite_web_of \<Gamma>)"
    by(rule bi.unhindered_linkable_bounded)
  then show ?thesis by(rule linkable_bipartite_web_ofD) simp
qed

lemma bounded_countable_web_quotient_web: "bounded_countable_web (quotient_web \<Gamma> f)" (is "bounded_countable_web ?\<Gamma>")
proof -
  interpret r: countable_web ?\<Gamma> by(rule countable_web_quotient_web)
  show ?thesis
  proof
    fix x
    assume "x \<in> \<^bold>V\<^bsub>quotient_web \<Gamma> f\<^esub> - B (quotient_web \<Gamma> f)"
    then have x: "x \<in> \<^bold>V - B \<Gamma>" by(auto dest: vertex_quotient_webD)
    have "(\<Sum>\<^sup>+ y \<in> \<^bold>E\<^bsub>?\<Gamma>\<^esub> `` {x}. weight ?\<Gamma> y) \<le> (\<Sum>\<^sup>+ y \<in> \<^bold>E `` {x}. weight \<Gamma> y)"
      by(auto simp add: nn_integral_count_space_indicator intro!: nn_integral_mono split: split_indicator)
    also have "\<dots> < \<top>" using x by(rule bounded_out)
    finally show "(\<Sum>\<^sup>+ y \<in> \<^bold>E\<^bsub>?\<Gamma>\<^esub> `` {x}. weight ?\<Gamma> y) < \<top>"  .
  qed
qed

lemma ex_orthogonal_current:
  "\<exists>f S. web_flow \<Gamma> f \<and> separating \<Gamma> S \<and> orthogonal_current \<Gamma> f S"
proof -
  from ex_maximal_wave[OF countable]
  obtain f where f: "current \<Gamma> f"
    and w: "wave \<Gamma> f"
    and maximal: "\<And>w. \<lbrakk> current \<Gamma> w; wave \<Gamma> w; f \<le> w \<rbrakk> \<Longrightarrow> f = w" by blast
  from ex_trimming[OF f w countable weight_finite] obtain h where h: "trimming \<Gamma> f h" ..

  let ?\<Gamma> = "quotient_web \<Gamma> f"
  interpret \<Gamma>: bounded_countable_web "?\<Gamma>" by(rule bounded_countable_web_quotient_web)
  have "loose ?\<Gamma>" using f w maximal by(rule loose_quotient_web[OF  weight_finite])
  then have "linkable ?\<Gamma>" by(rule \<Gamma>.loose_linkable_bounded)
  then obtain g where wg: "web_flow ?\<Gamma> g" and link: "linkage ?\<Gamma> g" by blast

  let ?k = "plus_current h g"
  have "web_flow \<Gamma> ?k" "orthogonal_current \<Gamma> ?k (\<E> (TER f))"
    by(rule linkage_quotient_webD[OF f w wg link h])+
  moreover have "separating \<Gamma> (\<E> (TER f))"
    using waveD_separating[OF w] by(rule separating_essential)
  ultimately show ?thesis by blast
qed

end

locale bounded_countable_network = countable_network \<Delta>
  for \<Delta> :: "('v, 'more) network_scheme" (structure) +
  assumes out: "\<lbrakk> x \<in> \<^bold>V; x \<noteq> source \<Delta> \<rbrakk> \<Longrightarrow> d_OUT (capacity \<Delta>) x < \<top>"

context antiparallel_edges begin

lemma \<Delta>''_bounded_countable_network: "bounded_countable_network \<Delta>''"
  if "\<And>x. \<lbrakk> x \<in> \<^bold>V; x \<noteq> source \<Delta> \<rbrakk> \<Longrightarrow> d_OUT (capacity \<Delta>) x < \<top>"
proof -
  interpret ae: countable_network \<Delta>'' by(rule \<Delta>''_countable_network)
  show ?thesis
  proof
    fix x
    assume x: "x \<in> \<^bold>V\<^bsub>\<Delta>''\<^esub>" and not_source: "x \<noteq> source \<Delta>''"
    from x consider (Vertex) x' where "x = Vertex x'" "x' \<in> \<^bold>V" | (Edge) y z where "x = Edge y z" "edge \<Delta> y z"
      unfolding "\<^bold>V_\<Delta>''" by auto
    then show "d_OUT (capacity \<Delta>'') x < \<top>"
    proof cases
      case Vertex
      then show ?thesis using x not_source that[of x'] by auto
    next
      case Edge
      then show ?thesis using capacity_finite[of "(y, z)"] by(simp del: capacity_finite add: less_top)
    qed
  qed
qed

end

context bounded_countable_network begin

lemma bounded_countable_web_web_of_network: 
  assumes source_in: "\<And>x. \<not> edge \<Delta> x (source \<Delta>)"
  and sink_out: "\<And>y. \<not> edge \<Delta> (sink \<Delta>) y"
  and undead: "\<And>x y. edge \<Delta> x y \<Longrightarrow> (\<exists>z. edge \<Delta> y z) \<or> (\<exists>z. edge \<Delta> z x)"
  and source_sink: "\<not> edge \<Delta> (source \<Delta>) (sink \<Delta>)"
  and no_loop: "\<And>x. \<not> edge \<Delta> x x"
  shows "bounded_countable_web (web_of_network \<Delta>)" (is "bounded_countable_web ?\<Gamma>")
proof -
  interpret web: countable_web ?\<Gamma> by(rule countable_web_web_of_network) fact+
  show ?thesis
  proof
    fix e
    assume "e \<in> \<^bold>V\<^bsub>?\<Gamma>\<^esub> - B ?\<Gamma>"
    then obtain x y where e: "e = (x, y)" and xy: "edge \<Delta> x y" by(cases e) simp
    from xy have y: "y \<noteq> source \<Delta>" using source_in[of x] by auto
    have "\<^bold>E\<^bsub>?\<Gamma>\<^esub> `` {e} \<subseteq> \<^bold>E \<inter> {y} \<times> UNIV" using e by auto
    hence "(\<Sum>\<^sup>+ e' \<in> \<^bold>E\<^bsub>?\<Gamma>\<^esub> `` {e}. weight ?\<Gamma> e') \<le> (\<Sum>\<^sup>+ e \<in> \<^bold>E \<inter> {y} \<times> UNIV. capacity \<Delta> e)" using e
      by(auto simp add: nn_integral_count_space_indicator intro!: nn_integral_mono split: split_indicator)
    also have "\<dots> \<le> (\<Sum>\<^sup>+ e \<in> Pair y ` UNIV. capacity \<Delta> e)"
      by(auto simp add: nn_integral_count_space_indicator intro!: nn_integral_mono split: split_indicator)
    also have "\<dots> = d_OUT (capacity \<Delta>) y" unfolding d_OUT_def
      by(rule nn_integral_count_space_reindex) simp
    also have "\<dots> < \<top>" using out[of y] xy y by(auto simp add: vertex_def)
    finally show "(\<Sum>\<^sup>+ e' \<in> \<^bold>E\<^bsub>?\<Gamma>\<^esub> `` {e}. weight ?\<Gamma> e') < \<top>" .
  qed
qed

context begin

qualified lemma max_flow_min_cut'_bounded:
  assumes source_in: "\<And>x. \<not> edge \<Delta> x (source \<Delta>)"
  and sink_out: "\<And>y. \<not> edge \<Delta> (sink \<Delta>) y"
  and undead: "\<And>x y. edge \<Delta> x y \<Longrightarrow> (\<exists>z. edge \<Delta> y z) \<or> (\<exists>z. edge \<Delta> z x)"
  and source_sink: "\<not> edge \<Delta> (source \<Delta>) (sink \<Delta>)"
  and no_loop: "\<And>x. \<not> edge \<Delta> x x"
  and capacity_pos: "\<And>e. e \<in> \<^bold>E \<Longrightarrow> capacity \<Delta> e > 0"
  shows "\<exists>f S. flow \<Delta> f \<and> cut \<Delta> S \<and> orthogonal \<Delta> f S"
  by(rule max_flow_min_cut')(rule bounded_countable_web.ex_orthogonal_current[OF bounded_countable_web_web_of_network], fact+)

qualified lemma max_flow_min_cut''_bounded:
  assumes sink_out: "\<And>y. \<not> edge \<Delta> (sink \<Delta>) y"
  and source_in: "\<And>x. \<not> edge \<Delta> x (source \<Delta>)"
  and no_loop: "\<And>x. \<not> edge \<Delta> x x"
  and capacity_pos: "\<And>e. e \<in> \<^bold>E \<Longrightarrow> capacity \<Delta> e > 0"
  shows "\<exists>f S. flow \<Delta> f \<and> cut \<Delta> S \<and> orthogonal \<Delta> f S"
proof -
  interpret antiparallel_edges \<Delta> ..
  interpret \<Delta>'': bounded_countable_network \<Delta>'' by(rule \<Delta>''_bounded_countable_network)(rule out)
  have "\<exists>f S. flow \<Delta>'' f \<and> cut \<Delta>'' S \<and> orthogonal \<Delta>'' f S"
    by(rule \<Delta>''.max_flow_min_cut'_bounded)(auto simp add: sink_out source_in no_loop capacity_pos elim: edg.cases)
  then obtain f S where f: "flow \<Delta>'' f" and cut: "cut \<Delta>'' S" and ortho: "orthogonal \<Delta>'' f S" by blast
  have "flow \<Delta> (collect f)" using f by(rule flow_collect)
  moreover have "cut \<Delta> (cut' S)" using cut by(rule cut_cut')
  moreover have "orthogonal \<Delta> (collect f) (cut' S)" using ortho f by(rule orthogonal_cut')
  ultimately show ?thesis by blast
qed

qualified lemma max_flow_min_cut'''_bounded:
  assumes sink_out: "\<And>y. \<not> edge \<Delta> (sink \<Delta>) y"
  and source_in: "\<And>x. \<not> edge \<Delta> x (source \<Delta>)"
  and capacity_pos: "\<And>e. e \<in> \<^bold>E \<Longrightarrow> capacity \<Delta> e > 0"
  shows "\<exists>f S. flow \<Delta> f \<and> cut \<Delta> S \<and> orthogonal \<Delta> f S"
proof -
  interpret antiparallel_edges \<Delta> ..
  interpret \<Delta>'': bounded_countable_network \<Delta>'' by(rule \<Delta>''_bounded_countable_network)(rule out)
  have "\<exists>f S. flow \<Delta>'' f \<and> cut \<Delta>'' S \<and> orthogonal \<Delta>'' f S"
    by(rule \<Delta>''.max_flow_min_cut''_bounded)(auto simp add: sink_out source_in capacity_pos elim: edg.cases)
  then obtain f S where f: "flow \<Delta>'' f" and cut: "cut \<Delta>'' S" and ortho: "orthogonal \<Delta>'' f S" by blast
  have "flow \<Delta> (collect f)" using f by(rule flow_collect)
  moreover have "cut \<Delta> (cut' S)" using cut by(rule cut_cut')
  moreover have "orthogonal \<Delta> (collect f) (cut' S)" using ortho f by(rule orthogonal_cut')
  ultimately show ?thesis by blast
qed

lemma \<Delta>'''_bounded_countable_network: "bounded_countable_network \<Delta>'''"
proof -
  interpret \<Delta>''': countable_network \<Delta>''' by(rule \<Delta>'''_countable_network)
  show ?thesis 
  proof
    fix x
    assume x: "x \<in> \<^bold>V\<^bsub>\<Delta>'''\<^esub>" and not_source: "x \<noteq> source \<Delta>'''"
    from x have x': "x \<in> \<^bold>V" by(auto simp add: vertex_def)
    have "d_OUT (capacity \<Delta>''') x \<le> d_OUT (capacity \<Delta>) x" by(rule d_OUT_mono) simp
    also have "\<dots> < \<top>" using x' not_source by(simp add: out)
    finally show "d_OUT (capacity \<Delta>''') x < \<top>"  .
  qed
qed

theorem max_flow_min_cut_bounded:
  "\<exists>f S. flow \<Delta> f \<and> cut \<Delta> S \<and> orthogonal \<Delta> f S"
proof -
  interpret \<Delta>': bounded_countable_network \<Delta>''' by(rule \<Delta>'''_bounded_countable_network)
  have "\<exists>f S. flow \<Delta>''' f \<and> cut \<Delta>''' S \<and> orthogonal \<Delta>''' f S" by(rule \<Delta>'.max_flow_min_cut'''_bounded) auto
  then obtain f S where f: "flow \<Delta>''' f" and cut: "cut \<Delta>''' S" and ortho: "orthogonal \<Delta>''' f S" by blast
  from flow_\<Delta>'''[OF this] show ?thesis by blast
qed

end

end

end
