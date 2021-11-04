theory MFMC_Web imports
  MFMC_Network
begin

section \<open>Webs and currents\<close>

record 'v web = "'v graph" +
  weight :: "'v \<Rightarrow> ennreal"
  A :: "'v set"
  B :: "'v set"

lemma vertex_weight_update [simp]: "vertex (weight_update f \<Gamma>) = vertex \<Gamma>"
by(simp add: vertex_def fun_eq_iff)

type_synonym 'v current = "'v edge \<Rightarrow> ennreal"

inductive current :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> bool"
  for \<Gamma> f
where
  current:
  "\<lbrakk> \<And>x. d_OUT f x \<le> weight \<Gamma> x;
     \<And>x. d_IN f x \<le> weight \<Gamma> x;
     \<And>x. x \<notin> A \<Gamma> \<Longrightarrow> d_OUT f x \<le> d_IN f x;
     \<And>a. a \<in> A \<Gamma> \<Longrightarrow> d_IN f a = 0;
     \<And>b. b \<in> B \<Gamma> \<Longrightarrow> d_OUT f b = 0;
     \<And>e. e \<notin> \<^bold>E\<^bsub>\<Gamma>\<^esub> \<Longrightarrow> f e = 0 \<rbrakk>
  \<Longrightarrow> current \<Gamma> f"

lemma currentD_weight_OUT: "current \<Gamma> f \<Longrightarrow> d_OUT f x \<le> weight \<Gamma> x"
by(simp add: current.simps)

lemma currentD_weight_IN: "current \<Gamma> f \<Longrightarrow> d_IN f x \<le> weight \<Gamma> x"
by(simp add: current.simps)

lemma currentD_OUT_IN: "\<lbrakk> current \<Gamma> f; x \<notin> A \<Gamma> \<rbrakk> \<Longrightarrow> d_OUT f x \<le> d_IN f x"
by(simp add: current.simps)

lemma currentD_IN: "\<lbrakk> current \<Gamma> f; a \<in> A \<Gamma> \<rbrakk> \<Longrightarrow> d_IN f a = 0"
by(simp add: current.simps)

lemma currentD_OUT: "\<lbrakk> current \<Gamma> f; b \<in> B \<Gamma> \<rbrakk> \<Longrightarrow> d_OUT f b = 0"
by(simp add: current.simps)

lemma currentD_outside: "\<lbrakk> current \<Gamma> f; \<not> edge \<Gamma> x y \<rbrakk> \<Longrightarrow> f (x, y) = 0"
by(blast elim: current.cases)

lemma currentD_outside': "\<lbrakk> current \<Gamma> f; e \<notin> \<^bold>E\<^bsub>\<Gamma>\<^esub> \<rbrakk> \<Longrightarrow> f e = 0"
by(blast elim: current.cases)

lemma currentD_OUT_eq_0:
  assumes "current \<Gamma> f"
  shows "d_OUT f x = 0 \<longleftrightarrow> (\<forall>y. f (x, y) = 0)"
by(simp add: d_OUT_def nn_integral_0_iff emeasure_count_space_eq_0)

lemma currentD_IN_eq_0:
  assumes "current \<Gamma> f"
  shows "d_IN f x = 0 \<longleftrightarrow> (\<forall>y. f (y, x) = 0)"
by(simp add: d_IN_def nn_integral_0_iff emeasure_count_space_eq_0)

lemma current_support_flow:
  fixes \<Gamma> (structure)
  assumes "current \<Gamma> f"
  shows "support_flow f \<subseteq> \<^bold>E"
using currentD_outside[OF assms] by(auto simp add: support_flow.simps intro: ccontr)

lemma currentD_outside_IN: "\<lbrakk> current \<Gamma> f; x \<notin> \<^bold>V\<^bsub>\<Gamma>\<^esub> \<rbrakk> \<Longrightarrow> d_IN f x = 0"
by(auto simp add: d_IN_def vertex_def nn_integral_0_iff  AE_count_space emeasure_count_space_eq_0 dest: currentD_outside)

lemma currentD_outside_OUT: "\<lbrakk> current \<Gamma> f; x \<notin> \<^bold>V\<^bsub>\<Gamma>\<^esub> \<rbrakk> \<Longrightarrow> d_OUT f x = 0"
by(auto simp add: d_OUT_def vertex_def nn_integral_0_iff  AE_count_space emeasure_count_space_eq_0 dest: currentD_outside)

lemma currentD_weight_in: "current \<Gamma> h \<Longrightarrow> h (x, y) \<le> weight \<Gamma> y"
  by (metis order_trans d_IN_ge_point currentD_weight_IN)

lemma currentD_weight_out: "current \<Gamma> h \<Longrightarrow> h (x, y) \<le> weight \<Gamma> x"
  by (metis order_trans d_OUT_ge_point currentD_weight_OUT)

lemma current_leI:
  fixes \<Gamma> (structure)
  assumes f: "current \<Gamma> f"
  and le: "\<And>e. g e \<le> f e"
  and OUT_IN: "\<And>x. x \<notin> A \<Gamma> \<Longrightarrow> d_OUT g x \<le> d_IN g x"
  shows "current \<Gamma> g"
proof
  show "d_OUT g x \<le> weight \<Gamma> x" for x
    using d_OUT_mono[of g x f, OF le] currentD_weight_OUT[OF f] by(rule order_trans)
  show "d_IN g x \<le> weight \<Gamma> x" for x
    using d_IN_mono[of g x f, OF le] currentD_weight_IN[OF f] by(rule order_trans)
  show "d_IN g a = 0" if "a \<in> A \<Gamma>" for a
    using d_IN_mono[of g a f, OF le] currentD_IN[OF f that] by auto
  show "d_OUT g b = 0" if "b \<in> B \<Gamma>" for b
    using d_OUT_mono[of g b f, OF le] currentD_OUT[OF f that] by auto
  show "g e = 0" if "e \<notin> \<^bold>E" for e
    using currentD_outside'[OF f that] le[of e] by simp
qed(blast intro: OUT_IN)+

lemma current_weight_mono:
  "\<lbrakk> current \<Gamma> f; edge \<Gamma> = edge \<Gamma>'; A \<Gamma> = A \<Gamma>'; B \<Gamma> = B \<Gamma>'; \<And>x. weight \<Gamma> x \<le> weight \<Gamma>' x \<rbrakk>
  \<Longrightarrow> current \<Gamma>' f"
by(auto 4 3 elim!: current.cases intro!: current.intros intro: order_trans)

abbreviation (input) zero_current :: "'v current"
where "zero_current \<equiv> \<lambda>_. 0"

lemma SINK_0 [simp]: "SINK zero_current = UNIV"
by(auto simp add: SINK.simps)

lemma current_0 [simp]: "current \<Gamma> zero_current"
by(auto simp add: current.simps)

inductive web_flow :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> bool"
  for \<Gamma> (structure) and f
where
  web_flow: "\<lbrakk> current \<Gamma> f; \<And>x. \<lbrakk> x \<in> \<^bold>V; x \<notin> A \<Gamma>; x \<notin> B \<Gamma> \<rbrakk> \<Longrightarrow> KIR f x \<rbrakk> \<Longrightarrow> web_flow \<Gamma> f"

lemma web_flowD_current: "web_flow \<Gamma> f \<Longrightarrow> current \<Gamma> f"
by(erule web_flow.cases)

lemma web_flowD_KIR: "\<lbrakk> web_flow \<Gamma> f; x \<notin> A \<Gamma>; x \<notin> B \<Gamma> \<rbrakk> \<Longrightarrow> KIR f x"
apply(cases "x \<in> \<^bold>V\<^bsub>\<Gamma>\<^esub>")
 apply(fastforce elim!: web_flow.cases)
apply(auto simp add: vertex_def d_OUT_def d_IN_def elim!: web_flow.cases)
apply(subst (1 2) currentD_outside[of _ f]; auto)
done

subsection \<open>Saturated and terminal vertices\<close>

inductive_set SAT :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> 'v set"
  for \<Gamma> f
where
  A: "x \<in> A \<Gamma> \<Longrightarrow> x \<in> SAT \<Gamma> f"
| IN: "d_IN f x \<ge> weight \<Gamma> x \<Longrightarrow> x \<in> SAT \<Gamma> f"
  \<comment> \<open>We use @{text "\<ge> weight"} such that @{text SAT} is monotone w.r.t. increasing currents\<close>

lemma SAT_0 [simp]: "SAT \<Gamma> zero_current = A \<Gamma> \<union> {x. weight \<Gamma> x \<le> 0}"
by(auto simp add: SAT.simps)

lemma SAT_mono:
  assumes "\<And>e. f e \<le> g e"
  shows "SAT \<Gamma> f \<subseteq> SAT \<Gamma> g"
proof
  fix x
  assume "x \<in> SAT \<Gamma> f"
  thus "x \<in> SAT \<Gamma> g"
  proof cases
    case IN
    also have "d_IN f x \<le> d_IN g x" using assms by(rule d_IN_mono)
    finally show ?thesis ..
  qed(rule SAT.A)
qed

lemma SAT_Sup_upper: "f \<in> Y \<Longrightarrow> SAT \<Gamma> f \<subseteq> SAT \<Gamma> (Sup Y)"
by(rule SAT_mono)(rule Sup_upper[THEN le_funD])

lemma currentD_SAT:
  assumes "current \<Gamma> f"
  shows "x \<in> SAT \<Gamma> f \<longleftrightarrow> x \<in> A \<Gamma> \<or> d_IN f x = weight \<Gamma> x"
using currentD_weight_IN[OF assms, of x] by(auto simp add: SAT.simps)

abbreviation terminal :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> 'v set" ("TER\<index>")
where "terminal \<Gamma> f \<equiv> SAT \<Gamma> f \<inter> SINK f"

subsection \<open>Separation\<close>

inductive separating_gen :: "('v, 'more) graph_scheme \<Rightarrow> 'v set \<Rightarrow> 'v set \<Rightarrow> 'v set \<Rightarrow> bool"
  for G A B S
where separating:
  "(\<And>x y p. \<lbrakk> x \<in> A; y \<in> B; path G x p y \<rbrakk> \<Longrightarrow> (\<exists>z \<in> set p. z \<in> S) \<or> x \<in> S)
  \<Longrightarrow> separating_gen G A B S"

abbreviation separating :: "('v, 'more) web_scheme \<Rightarrow> 'v set \<Rightarrow> bool"
where "separating \<Gamma> \<equiv> separating_gen \<Gamma> (A \<Gamma>) (B \<Gamma>)"

abbreviation separating_network :: "('v, 'more) network_scheme \<Rightarrow> 'v set \<Rightarrow> bool"
where "separating_network \<Delta> \<equiv> separating_gen \<Delta> {source \<Delta>} {sink \<Delta>}"

lemma separating_networkI [intro?]:
  "(\<And>p. path \<Delta> (source \<Delta>) p (sink \<Delta>) \<Longrightarrow> (\<exists>z \<in> set p. z \<in> S) \<or> source \<Delta> \<in> S)
  \<Longrightarrow> separating_network \<Delta> S"
by(auto intro: separating)

lemma separatingD:
  "\<And>A B. \<lbrakk> separating_gen G A B S; path G x p y; x \<in> A; y \<in> B \<rbrakk> \<Longrightarrow> (\<exists>z \<in> set p. z \<in> S) \<or> x \<in> S"
by(blast elim: separating_gen.cases)

lemma separating_left [simp]: "\<And>A B. A \<subseteq> A' \<Longrightarrow> separating_gen \<Gamma> A B A'"
by(auto simp add: separating_gen.simps)

lemma separating_weakening:
  "\<And>A B. \<lbrakk> separating_gen G A B S; S \<subseteq> S' \<rbrakk> \<Longrightarrow> separating_gen G A B S'"
by(rule separating; drule (3) separatingD; blast)

definition essential :: "('v, 'more) graph_scheme \<Rightarrow> 'v set \<Rightarrow> 'v set \<Rightarrow> 'v \<Rightarrow> bool"
where \<comment> \<open>Should we allow only simple paths here?\<close>
  "\<And>B. essential G B S x \<longleftrightarrow> (\<exists>p. \<exists>y\<in>B. path G x p y \<and> (x \<noteq> y \<longrightarrow> (\<forall>z\<in>set p. z = x \<or> z \<notin> S)))"

abbreviation essential_web :: "('v, 'more) web_scheme \<Rightarrow> 'v set \<Rightarrow> 'v set" ("\<E>\<index>")
where "essential_web \<Gamma> S \<equiv> {x\<in>S. essential \<Gamma> (B \<Gamma>) S x}"

lemma essential_weight_update [simp]:
  "essential (weight_update f G) = essential G"
by(simp add: essential_def fun_eq_iff)

lemma not_essentialD:
  "\<And>B. \<lbrakk> \<not> essential G B S x; path G x p y; y \<in> B \<rbrakk> \<Longrightarrow> x \<noteq> y \<and> (\<exists>z\<in>set p. z \<noteq> x \<and> z \<in> S)"
by(simp add: essential_def)

lemma essentialE [elim?, consumes 1, case_names essential, cases pred: essential]:
  "\<And>B. \<lbrakk> essential G B S x; \<And>p y. \<lbrakk> path G x p y; y \<in> B; \<And>z. \<lbrakk> x \<noteq> y; z \<in> set p \<rbrakk> \<Longrightarrow> z = x \<or> z \<notin> S \<rbrakk> \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
by(auto simp add: essential_def)

lemma essentialI [intro?]:
  "\<And>B. \<lbrakk> path G x p y; y \<in> B; \<And>z. \<lbrakk> x \<noteq> y; z \<in> set p \<rbrakk> \<Longrightarrow> z = x \<or> z \<notin> S \<rbrakk> \<Longrightarrow> essential G B S x"
by(auto simp add: essential_def)

lemma essential_vertex: "\<And>B. \<lbrakk> essential G B S x; x \<notin> B \<rbrakk> \<Longrightarrow>vertex G x"
by(auto elim!: essentialE simp add: vertex_def elim: rtrancl_path.cases)

lemma essential_BI: "\<And>B. x \<in> B \<Longrightarrow> essential G B S x"
by(auto simp add: essential_def intro: rtrancl_path.base)

lemma \<E>_E [elim?, consumes 1, case_names \<E>, cases set: essential_web]:
  fixes \<Gamma> (structure)
  assumes "x \<in> \<E> S"
  obtains p y where "path \<Gamma> x p y" "y \<in> B \<Gamma>" "\<And>z. \<lbrakk> x \<noteq> y; z \<in> set p \<rbrakk> \<Longrightarrow> z = x \<or> z \<notin> S"
using assms by(auto elim: essentialE)

lemma essential_mono: "\<And>B. \<lbrakk> essential G B S x; S' \<subseteq> S \<rbrakk> \<Longrightarrow> essential G B S' x"
by(auto simp add: essential_def)

lemma separating_essential: \<comment> \<open>Lem. 3.4 (cf. Lem. 2.14 in [5])\<close>
  fixes G A B S
  assumes "separating_gen G A B S"
  shows "separating_gen G A B {x\<in>S. essential G B S x}" (is "separating_gen _ _ _ ?E")
proof
  fix x y p
  assume x: "x \<in> A" and y: "y \<in> B" and p: "path G x p y"
  from separatingD[OF assms p x y] have "\<exists>z \<in> set (x # p). z \<in> S" by auto
  from split_list_last_prop[OF this] obtain ys z zs where decomp: "x # p = ys @ z # zs"
    and z: "z \<in> S" and last: "\<And>z. z \<in> set zs \<Longrightarrow> z \<notin> S" by auto
  from decomp consider (empty) "ys = []" "x = z" "p = zs"
    | (Cons) ys' where "ys = x # ys'" "p = ys' @ z # zs"
    by(auto simp add: Cons_eq_append_conv)
  then show "(\<exists>z\<in>set p. z \<in> ?E) \<or> x \<in> ?E"
  proof(cases)
    case empty
    hence "x \<in> ?E" using z p last y by(auto simp add: essential_def)
    thus ?thesis ..
  next
    case (Cons ys')
    from p have "path G z zs y" unfolding Cons by(rule rtrancl_path_appendE)
    hence "z \<in> ?E" using z y last by(auto simp add: essential_def)
    thus ?thesis using Cons by auto
  qed
qed

definition roofed_gen :: "('v, 'more) graph_scheme \<Rightarrow> 'v set \<Rightarrow> 'v set \<Rightarrow> 'v set"
where roofed_def: "\<And>B. roofed_gen G B S = {x. \<forall>p. \<forall>y\<in>B. path G x p y \<longrightarrow> (\<exists>z\<in>set p. z \<in> S) \<or> x \<in> S}"

abbreviation roofed :: "('v, 'more) web_scheme \<Rightarrow> 'v set \<Rightarrow> 'v set" ("RF\<index>")
where "roofed \<Gamma> \<equiv> roofed_gen \<Gamma> (B \<Gamma>)"

abbreviation roofed_network :: "('v, 'more) network_scheme \<Rightarrow> 'v set \<Rightarrow> 'v set" ("RF\<^sup>N\<index>")
where "roofed_network \<Delta> \<equiv> roofed_gen \<Delta> {sink \<Delta>}"

lemma roofedI [intro?]:
  "\<And>B. (\<And>p y. \<lbrakk> path G x p y; y \<in> B \<rbrakk> \<Longrightarrow> (\<exists>z\<in>set p. z \<in> S) \<or> x \<in> S) \<Longrightarrow> x \<in> roofed_gen G B S"
by(auto simp add: roofed_def)

lemma not_roofedE: fixes B
  assumes "x \<notin> roofed_gen G B S"
  obtains p y where "path G x p y" "y \<in> B" "\<And>z. z \<in> set (x # p) \<Longrightarrow> z \<notin> S"
using assms by(auto simp add: roofed_def)

lemma roofed_greater: "\<And>B. S \<subseteq> roofed_gen G B S"
by(auto simp add: roofed_def)

lemma roofed_greaterI: "\<And>B. x \<in> S \<Longrightarrow> x \<in> roofed_gen G B S"
using roofed_greater[of S G] by blast

lemma roofed_mono: "\<And>B. S \<subseteq> S' \<Longrightarrow> roofed_gen G B S \<subseteq> roofed_gen G B S'"
by(fastforce simp add: roofed_def)

lemma in_roofed_mono: "\<And>B. \<lbrakk> x \<in> roofed_gen G B S; S \<subseteq> S' \<rbrakk> \<Longrightarrow> x \<in> roofed_gen G B S'"
using roofed_mono[THEN subsetD] .

lemma roofedD: "\<And>B. \<lbrakk> x \<in> roofed_gen G B S; path G x p y; y \<in> B \<rbrakk> \<Longrightarrow> (\<exists>z\<in>set p. z \<in> S) \<or> x \<in> S"
unfolding roofed_def by blast

lemma separating_RF_A:
  fixes A B
  assumes "separating_gen G A B X"
  shows "A \<subseteq> roofed_gen G B X"
by(rule subsetI roofedI)+(erule separatingD[OF assms])

lemma roofed_idem: fixes B shows "roofed_gen G B (roofed_gen G B S) = roofed_gen G B S"
proof(rule equalityI subsetI roofedI)+
  fix x p y
  assume x: "x \<in> roofed_gen G B (roofed_gen G B S)" and p: "path G x p y" and y: "y \<in> B"
  from roofedD[OF x p y] obtain z where *: "z \<in> set (x # p)" and z: "z \<in> roofed_gen G B S" by auto
  from split_list[OF *] obtain ys zs where split: "x # p = ys @ z # zs" by blast
  with p have p': "path G z zs y" by(auto simp add: Cons_eq_append_conv elim: rtrancl_path_appendE)
  from roofedD[OF z p' y] split show "(\<exists>z\<in>set p. z \<in> S) \<or> x \<in> S"
    by(auto simp add: Cons_eq_append_conv)
qed(rule roofed_mono roofed_greater)+

lemma in_roofed_mono': "\<And>B. \<lbrakk> x \<in> roofed_gen G B S; S \<subseteq> roofed_gen G B S' \<rbrakk> \<Longrightarrow> x \<in> roofed_gen G B S'"
by(subst roofed_idem[symmetric])(erule in_roofed_mono)

lemma roofed_mono': "\<And>B. S \<subseteq> roofed_gen G B S' \<Longrightarrow> roofed_gen G B S \<subseteq> roofed_gen G B S'"
by(rule subsetI)(rule in_roofed_mono')

lemma roofed_idem_Un1: fixes B shows "roofed_gen G B (roofed_gen G B S \<union> T) = roofed_gen G B (S \<union> T)"
proof -
  have "S \<subseteq> T \<union> roofed_gen G B S"
    by (metis (no_types) UnCI roofed_greater subsetCE subsetI)
  then have "S \<union> T \<subseteq> T \<union> roofed_gen G B S \<and> T \<union> roofed_gen G B S \<subseteq> roofed_gen G B (S \<union> T)"
    by (metis (no_types) Un_subset_iff Un_upper2 roofed_greater roofed_mono sup.commute)
  then show ?thesis
    by (metis (no_types) roofed_idem roofed_mono subset_antisym sup.commute)
qed

lemma roofed_UN: fixes A B
  shows "roofed_gen G B (\<Union>i\<in>A. roofed_gen G B (X i)) = roofed_gen G B (\<Union>i\<in>A. X i)" (is "?lhs = ?rhs")
proof(rule equalityI)
  show "?rhs \<subseteq> ?lhs" by(rule roofed_mono)(blast intro: roofed_greaterI)
  show "?lhs \<subseteq> ?rhs" by(rule roofed_mono')(blast intro: in_roofed_mono)
qed

lemma RF_essential: fixes \<Gamma> (structure) shows "RF (\<E> S) = RF S"
proof(intro set_eqI iffI)
  fix x
  assume RF: "x \<in> RF S"
  show "x \<in> RF (\<E> S)"
  proof
    fix p y
    assume p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
    from roofedD[OF RF this] have "\<exists>z\<in>set (x # p). z \<in> S" by auto
    from split_list_last_prop[OF this] obtain ys z zs where decomp: "x # p = ys @ z # zs"
      and z: "z \<in> S" and last: "\<And>z. z \<in> set zs \<Longrightarrow> z \<notin> S" by auto
    from decomp consider (empty) "ys = []" "x = z" "p = zs"
      | (Cons) ys' where "ys = x # ys'" "p = ys' @ z # zs"
      by(auto simp add: Cons_eq_append_conv)
    then show "(\<exists>z\<in>set p. z \<in> \<E> S) \<or> x \<in> \<E> S"
    proof(cases)
      case empty
      hence "x \<in> \<E> S" using z p last y by(auto simp add: essential_def)
      thus ?thesis ..
    next
      case (Cons ys')
      from p have "path \<Gamma> z zs y" unfolding Cons by(rule rtrancl_path_appendE)
      hence "z \<in> \<E> S" using z y last by(auto simp add: essential_def)
      thus ?thesis using Cons by auto
    qed
  qed
qed(blast intro: in_roofed_mono)

lemma essentialE_RF:
  fixes \<Gamma> (structure) and B
  assumes "essential \<Gamma> B S x"
  obtains p y where "path \<Gamma> x p y" "y \<in> B" "distinct (x # p)" "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> roofed_gen \<Gamma> B S"
proof -
  from assms obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B"
    and bypass: "\<And>z. \<lbrakk> x \<noteq> y; z \<in> set p \<rbrakk> \<Longrightarrow> z = x \<or> z \<notin> S" by(rule essentialE) blast
  from p obtain p' where p': "path \<Gamma> x p' y" and distinct: "distinct (x # p')"
    and subset: "set p' \<subseteq> set p" by(rule rtrancl_path_distinct)
  { fix z
    assume z: "z \<in> set p'"
    hence "y \<in> set p'" using rtrancl_path_last[OF p', symmetric] p'
      by(auto elim: rtrancl_path.cases intro: last_in_set)
    with distinct z subset have neq: "x \<noteq> y" and "z \<in> set p" by(auto)
    from bypass[OF this] z distinct have "z \<notin> S" by auto

    have "z \<notin> roofed_gen \<Gamma> B S"
    proof
      assume z': "z \<in> roofed_gen \<Gamma> B S"
      from split_list[OF z] obtain ys zs where decomp: "p' = ys @ z # zs" by blast
      with p' have "path \<Gamma> z zs y" by(auto elim: rtrancl_path_appendE)
      from roofedD[OF z' this y] \<open>z \<notin> S\<close> obtain z' where "z' \<in> set zs" "z' \<in> S" by auto
      with bypass[of z'] neq decomp subset distinct show False by auto
    qed }
  with p' y distinct show thesis ..
qed

lemma \<E>_E_RF:
  fixes \<Gamma> (structure)
  assumes "x \<in> \<E> S"
  obtains p y where "path \<Gamma> x p y" "y \<in> B \<Gamma>" "distinct (x # p)" "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF S"
using assms by(auto elim: essentialE_RF)

lemma in_roofed_essentialD:
  fixes \<Gamma> (structure)
  assumes RF: "x \<in> RF S"
  and ess: "essential \<Gamma> (B \<Gamma>) S x"
  shows "x \<in> S"
proof -
  from ess obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>" and "distinct (x # p)"
    and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> S" by(rule essentialE_RF)(auto intro: roofed_greaterI)
  from roofedD[OF RF p y] bypass show "x \<in> S" by auto
qed

lemma separating_RF: fixes \<Gamma> (structure) shows "separating \<Gamma> (RF S) \<longleftrightarrow> separating \<Gamma> S"
proof
  assume sep: "separating \<Gamma> (RF S)"
  show "separating \<Gamma> S"
  proof
    fix x y p
    assume p: "path \<Gamma> x p y" and x: "x \<in> A \<Gamma>" and y: "y \<in> B \<Gamma>"
    from separatingD[OF sep p x y] have "\<exists>z \<in> set (x # p). z \<in> RF S" by auto
    from split_list_last_prop[OF this] obtain ys z zs where split: "x # p = ys @ z # zs"
      and z: "z \<in> RF S" and bypass: "\<And>z'. z' \<in> set zs \<Longrightarrow> z' \<notin> RF S" by auto
    from p split have "path \<Gamma> z zs y" by(cases ys)(auto elim: rtrancl_path_appendE)
    hence "essential \<Gamma> (B \<Gamma>) S z" using y
      by(rule essentialI)(auto dest: bypass intro: roofed_greaterI)
    with z have "z \<in> S" by(rule in_roofed_essentialD)
    with split show "(\<exists>z\<in>set p. z \<in> S) \<or> x \<in> S" by(cases ys)auto
  qed
qed(blast intro: roofed_greaterI separating_weakening)

definition roofed_circ :: "('v, 'more) web_scheme \<Rightarrow> 'v set \<Rightarrow> 'v set" ("RF\<^sup>\<circ>\<index>")
where "roofed_circ \<Gamma> S = roofed \<Gamma> S - \<E>\<^bsub>\<Gamma>\<^esub> S"

lemma roofed_circI: fixes \<Gamma> (structure) shows
  "\<lbrakk> x \<in> RF T; x \<in> T \<Longrightarrow> \<not> essential \<Gamma> (B \<Gamma>) T x \<rbrakk> \<Longrightarrow> x \<in> RF\<^sup>\<circ> T"
by(simp add: roofed_circ_def)

lemma roofed_circE:
  fixes \<Gamma> (structure)
  assumes "x \<in> RF\<^sup>\<circ> T"
  obtains "x \<in> RF T" "\<not> essential \<Gamma> (B \<Gamma>) T x"
using assms by(auto simp add: roofed_circ_def intro: in_roofed_essentialD)

lemma \<E>_\<E>: fixes \<Gamma> (structure) shows "\<E> (\<E> S) = \<E> S"
by(auto intro: essential_mono)

lemma roofed_circ_essential: fixes \<Gamma> (structure) shows "RF\<^sup>\<circ> (\<E> S) = RF\<^sup>\<circ> S"
unfolding roofed_circ_def RF_essential \<E>_\<E> ..

lemma essential_RF: fixes B
  shows "essential G B (roofed_gen G B S) = essential G B S"  (is "essential _ _ ?RF = _")
proof(intro ext iffI)
  show "essential G B S x" if "essential G B ?RF x" for x using that
    by(rule essential_mono)(blast intro: roofed_greaterI)
  show "essential G B ?RF x" if "essential G B S x" for x
    using that by(rule essentialE_RF)(erule (1) essentialI, blast)
qed

lemma \<E>_RF: fixes \<Gamma> (structure) shows "\<E> (RF S) = \<E> S"
by(auto dest: in_roofed_essentialD simp add: essential_RF intro: roofed_greaterI)

lemma essential_\<E>: fixes \<Gamma> (structure) shows "essential \<Gamma> (B \<Gamma>) (\<E> S) = essential \<Gamma> (B \<Gamma>) S"
by(subst essential_RF[symmetric])(simp only: RF_essential essential_RF)

lemma RF_in_B: fixes \<Gamma> (structure) shows "x \<in> B \<Gamma> \<Longrightarrow> x \<in> RF S \<longleftrightarrow> x \<in> S"
by(auto intro: roofed_greaterI dest: roofedD[OF _ rtrancl_path.base])

lemma RF_circ_edge_forward:
  fixes \<Gamma> (structure)
  assumes x: "x \<in> RF\<^sup>\<circ> S"
  and edge: "edge \<Gamma> x y"
  shows "y \<in> RF S"
proof
  fix p z
  assume p: "path \<Gamma> y p z" and z: "z \<in> B \<Gamma>"
  from x have rf: "x \<in> RF S" and ness: "x \<notin> \<E> S" by(auto elim: roofed_circE)
  show "(\<exists>z\<in>set p. z \<in> S) \<or> y \<in> S"
  proof(cases "\<exists>z'\<in>set (y # p). z' \<in> S")
    case False
    from edge p have p': "path \<Gamma> x (y # p) z" ..
    from roofedD[OF rf this z] False have "x \<in> S" by auto
    moreover have "essential \<Gamma> (B \<Gamma>) S x" using p' False z by(auto intro!: essentialI)
    ultimately have "x \<in> \<E> S" by simp
    with ness show ?thesis by contradiction
  qed auto
qed

subsection \<open>Waves\<close>

inductive wave :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> bool"
  for \<Gamma> (structure) and f
where
  wave:
  "\<lbrakk> separating \<Gamma> (TER f);
     \<And>x. x \<notin> RF (TER f) \<Longrightarrow> d_OUT f x = 0 \<rbrakk>
  \<Longrightarrow> wave \<Gamma> f"

lemma wave_0 [simp]: "wave \<Gamma> zero_current"
by rule simp_all

lemma waveD_separating: "wave \<Gamma> f \<Longrightarrow> separating \<Gamma> (TER\<^bsub>\<Gamma>\<^esub> f)"
by(simp add: wave.simps)

lemma waveD_OUT: "\<lbrakk> wave \<Gamma> f; x \<notin> RF\<^bsub>\<Gamma>\<^esub> (TER\<^bsub>\<Gamma>\<^esub> f) \<rbrakk> \<Longrightarrow> d_OUT f x = 0"
by(simp add: wave.simps)

lemma wave_A_in_RF: fixes \<Gamma> (structure)
  shows "\<lbrakk> wave \<Gamma> f; x \<in> A \<Gamma> \<rbrakk> \<Longrightarrow> x \<in> RF (TER f)"
by(auto intro!: roofedI dest!: waveD_separating separatingD)

lemma wave_not_RF_IN_zero:
  fixes \<Gamma> (structure)
  assumes f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  and x: "x \<notin> RF (TER f)"
  shows "d_IN f x = 0"
proof -
  from x obtain p z where z: "z \<in> B \<Gamma>" and p: "path \<Gamma> x p z"
    and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> TER f" "x \<notin> TER f"
    by(clarsimp simp add: roofed_def)
  have "f (y, x) = 0" for y
  proof(cases "edge \<Gamma> y x")
    case edge: True
    have "d_OUT f y = 0"
    proof(cases "y \<in> TER f")
      case False
      with z p bypass edge have "y \<notin> RF (TER f)"
        by(auto simp add: roofed_def intro: rtrancl_path.step intro!: exI rev_bexI)
      thus "d_OUT f y = 0" by(rule waveD_OUT[OF w])
    qed(auto simp add: SINK.simps)
    moreover have "f (y, x) \<le> d_OUT f y" by (rule d_OUT_ge_point)
    ultimately show ?thesis by simp
  qed(simp add: currentD_outside[OF f])
  then show "d_IN f x = 0" unfolding d_IN_def
    by(simp add: nn_integral_0_iff emeasure_count_space_eq_0)
qed

lemma current_Sup:
  fixes \<Gamma> (structure)
  assumes chain: "Complete_Partial_Order.chain (\<le>) Y"
  and Y: "Y \<noteq> {}"
  and current: "\<And>f. f \<in> Y \<Longrightarrow> current \<Gamma> f"
  and countable [simp]: "countable (support_flow (Sup Y))"
  shows "current \<Gamma> (Sup Y)"
proof(rule, goal_cases)
  case (1 x)
  have "d_OUT (Sup Y) x = (SUP f\<in>Y. d_OUT f x)" using chain Y by(simp add: d_OUT_Sup)
  also have "\<dots> \<le> weight \<Gamma> x" using 1
    by(intro SUP_least)(auto dest!: current currentD_weight_OUT)
  finally show ?case .
next
  case (2 x)
  have "d_IN (Sup Y) x = (SUP f\<in>Y. d_IN f x)" using chain Y by(simp add: d_IN_Sup)
  also have "\<dots> \<le> weight \<Gamma> x" using 2
    by(intro SUP_least)(auto dest!: current currentD_weight_IN)
  finally show ?case .
next
  case (3 x)
  have "d_OUT (Sup Y) x = (SUP f\<in>Y. d_OUT f x)" using chain Y by(simp add: d_OUT_Sup)
  also have "\<dots> \<le> (SUP f\<in>Y. d_IN f x)" using 3
    by(intro SUP_mono)(auto dest: current currentD_OUT_IN)
  also have "\<dots> = d_IN (Sup Y) x" using chain Y by(simp add: d_IN_Sup)
  finally show ?case .
next
  case (4 a)
  have "d_IN (Sup Y) a = (SUP f\<in>Y. d_IN f a)" using chain Y by(simp add: d_IN_Sup)
  also have "\<dots> = (SUP f\<in>Y. 0)" using 4 by(intro SUP_cong)(auto dest!: current currentD_IN)
  also have "\<dots> = 0" using Y by simp
  finally show ?case .
next
  case (5 b)
  have "d_OUT (Sup Y) b = (SUP f\<in>Y. d_OUT f b)" using chain Y by(simp add: d_OUT_Sup)
  also have "\<dots> = (SUP f\<in>Y. 0)" using 5 by(intro SUP_cong)(auto dest!: current currentD_OUT)
  also have "\<dots> = 0" using Y by simp
  finally show ?case .
next
  fix e
  assume "e \<notin> \<^bold>E"
  from currentD_outside'[OF current this] have "f e = 0" if "f \<in> Y" for f using that by simp
  hence "Sup Y e = (SUP _\<in>Y. 0)" by(auto intro: SUP_cong)
  then show "Sup Y e = 0" using Y by(simp)
qed

lemma wave_lub: \<comment> \<open>Lemma 4.3\<close>
  fixes \<Gamma> (structure)
  assumes chain: "Complete_Partial_Order.chain (\<le>) Y"
  and Y: "Y \<noteq> {}"
  and wave: "\<And>f. f \<in> Y \<Longrightarrow> wave \<Gamma> f"
  and countable [simp]: "countable (support_flow (Sup Y))"
  shows "wave \<Gamma> (Sup Y)"
proof
  { fix x y p
    assume p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
    define P where "P = {x} \<union> set p"

    let ?f = "\<lambda>f. SINK f \<inter> P"
    have "Complete_Partial_Order.chain (\<supseteq>) (?f ` Y)" using chain
      by(rule chain_imageI)(auto dest: SINK_mono')
    moreover have "\<dots> \<subseteq> Pow P" by auto
    hence "finite (?f ` Y)" by(rule finite_subset)(simp add: P_def)
    ultimately have "(\<Inter>(?f ` Y)) \<in> ?f ` Y"
      by(rule ccpo.in_chain_finite[OF complete_lattice_ccpo_dual])(simp add: Y)
    then obtain f where f: "f \<in> Y" and eq: "\<Inter>(?f ` Y) = ?f f" by clarify
    hence *: "(\<Inter>f\<in>Y. SINK f) \<inter> P = SINK f \<inter> P" by(clarsimp simp add: prod_lub_def Y)+
    { fix g
      assume "g \<in> Y" "f \<le> g"
      with * have "(\<Inter>f\<in>Y. SINK f) \<inter> P = SINK g \<inter> P" by(blast dest: SINK_mono')
      then have "TER (Sup Y) \<inter> P \<supseteq> TER g \<inter> P"
        using SAT_Sup_upper[OF \<open>g \<in> Y\<close>, of \<Gamma>] SINK_Sup[OF chain Y countable] by blast }
    with f have "\<exists>f\<in>Y. \<forall>g\<in>Y. g \<ge> f \<longrightarrow> TER g \<inter> P \<subseteq> TER (Sup Y) \<inter> P" by blast }
  note subset = this

  show "separating \<Gamma> (TER (Sup Y))"
  proof
    fix x y p
    assume *: "path \<Gamma> x p y" "y \<in> B \<Gamma>" and "x \<in> A \<Gamma>"
    let ?P = "{x} \<union> set p"
    from subset[OF *] obtain f where f:"f \<in> Y"
      and subset: "TER f \<inter> ?P \<subseteq> TER (Sup Y) \<inter> ?P" by blast
    from wave[OF f] have "TER f \<inter> ?P \<noteq> {}" using * \<open>x \<in> A \<Gamma>\<close>
      by(auto simp add: wave.simps dest: separatingD)
    with subset show " (\<exists>z\<in>set p. z \<in> TER (Sup Y)) \<or> x \<in> TER (Sup Y)" by blast
  qed

  fix x
  assume "x \<notin> RF (TER (Sup Y))"
  then obtain p y where y: "y \<in> B \<Gamma>"
    and p: "path \<Gamma> x p y"
    and ter: "TER (Sup Y) \<inter> ({x} \<union> set p) = {}" by(auto simp add: roofed_def)
  let ?P = "{x} \<union> set p"
  from subset[OF p y] obtain f where f: "f \<in> Y"
    and subset: "\<And>g. \<lbrakk> g \<in> Y; f \<le> g \<rbrakk> \<Longrightarrow> TER g \<inter> ?P \<subseteq> TER (Sup Y) \<inter> ?P" by blast

  { fix g
    assume g: "g \<in> Y"
    with chain f have "f \<le> g \<or> g \<le> f" by(rule chainD)
    hence "d_OUT g x = 0"
    proof
      assume "f \<le> g"
      from subset[OF g this] ter have "TER g \<inter> ?P = {}" by blast
      with p y have "x \<notin> RF (TER g)" by(auto simp add: roofed_def)
      with wave[OF g] show ?thesis by(blast elim: wave.cases)
    next
      assume "g \<le> f"
      from subset ter f have "TER f \<inter> ?P = {}" by blast
      with y p have "x \<notin> RF (TER f)" by(auto simp add: roofed_def)
      with wave[OF f] have "d_OUT f x = 0" by(blast elim: wave.cases)
      moreover have "d_OUT g x \<le> d_OUT f x" using \<open>g \<le> f\<close>[THEN le_funD] by(rule d_OUT_mono)
      ultimately show ?thesis by simp
    qed }
  thus "d_OUT (Sup Y) x = 0" using chain Y by(simp add: d_OUT_Sup)
qed

lemma ex_maximal_wave: \<comment> \<open>Corollary 4.4\<close>
  fixes \<Gamma> (structure)
  assumes countable: "countable \<^bold>E"
  shows "\<exists>f. current \<Gamma> f \<and> wave \<Gamma> f \<and> (\<forall>w. current \<Gamma> w \<and> wave \<Gamma> w \<and> f \<le> w \<longrightarrow> f = w)"
proof -
  define Field_r where "Field_r = {f. current \<Gamma> f \<and> wave \<Gamma> f}"
  define r where "r = {(f, g). f \<in> Field_r \<and> g \<in> Field_r \<and> f \<le> g}"
  have Field_r: "Field r = Field_r" by(auto simp add: Field_def r_def)

  have "Partial_order r" unfolding order_on_defs
    by(auto intro!: refl_onI transI antisymI simp add: Field_r r_def Field_def)
  hence "\<exists>m\<in>Field r. \<forall>a\<in>Field r. (m, a) \<in> r \<longrightarrow> a = m"
  proof(rule Zorns_po_lemma)
    fix Y
    assume "Y \<in> Chains r"
    hence Y: "Complete_Partial_Order.chain (\<le>) Y"
      and w: "\<And>f. f \<in> Y \<Longrightarrow> wave \<Gamma> f"
      and f: "\<And>f. f \<in> Y \<Longrightarrow> current \<Gamma> f"
      by(auto simp add: Chains_def r_def chain_def Field_r_def)
    show "\<exists>w \<in> Field r. \<forall>f \<in> Y. (f, w) \<in> r"
    proof(cases "Y = {}")
      case True
      have "zero_current \<in> Field r" by(simp add: Field_r Field_r_def)
      with True show ?thesis by blast
    next
      case False
      have "support_flow (Sup Y) \<subseteq> \<^bold>E" by(auto simp add: support_flow_Sup elim!: support_flow.cases dest!: f dest: currentD_outside)
      hence c: "countable (support_flow (Sup Y))" using countable  by(rule countable_subset)
      with Y False f w have "Sup Y \<in> Field r" unfolding Field_r Field_r_def
        by(blast intro: wave_lub current_Sup)
      moreover then have "(f, Sup Y) \<in> r" if "f \<in> Y" for f using w[OF that] f[OF that] that unfolding Field_r
        by(auto simp add: r_def Field_r_def intro: Sup_upper)
      ultimately show ?thesis by blast
    qed
  qed
  thus ?thesis by(simp add: Field_r Field_r_def)(auto simp add: r_def Field_r_def)
qed

lemma essential_leI:
  fixes \<Gamma> (structure)
  assumes g: "current \<Gamma> g" and w: "wave \<Gamma> g"
  and le: "\<And>e. f e \<le> g e"
  and x: "x \<in> \<E> (TER g)"
  shows "essential \<Gamma> (B \<Gamma>) (TER f) x"
proof -
  from x obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>" and distinct: "distinct (x # p)"
    and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER g)" by(rule \<E>_E_RF) blast
  show ?thesis using p y
  proof
    fix z
    assume "z \<in> set p"
    hence z: "z \<notin> RF (TER g)" by(auto dest: bypass)
    with w have OUT: "d_OUT g z = 0" and IN: "d_IN g z = 0" by(rule waveD_OUT wave_not_RF_IN_zero[OF g])+
    with z have "z \<notin> A \<Gamma>" "weight \<Gamma> z > 0" by(auto intro!: roofed_greaterI simp add: SAT.simps SINK.simps)
    moreover from IN d_IN_mono[of f z g, OF le] have "d_IN f z \<le> 0" by(simp)
    ultimately have "z \<notin> TER f" by(auto simp add: SAT.simps)
    then show "z = x \<or> z \<notin> TER f" by simp
  qed
qed

lemma essential_eq_leI:
  fixes \<Gamma> (structure)
  assumes g: "current \<Gamma> g" and w: "wave \<Gamma> g"
  and le: "\<And>e. f e \<le> g e"
  and subset: "\<E> (TER g) \<subseteq> TER f"
  shows "\<E> (TER f) = \<E> (TER g)"
proof
  show subset: "\<E> (TER g) \<subseteq> \<E> (TER f)"
  proof
    fix x
    assume x: "x \<in> \<E> (TER g)"
    hence "x \<in> TER f" using subset by blast
    moreover have "essential \<Gamma> (B \<Gamma>) (TER f) x" using g w le x by(rule essential_leI)
    ultimately show "x \<in> \<E> (TER f)" by simp
  qed

  show "\<dots> \<subseteq> \<E> (TER g)"
  proof
    fix x
    assume x: "x \<in> \<E> (TER f)"
    hence "x \<in> TER f" by auto
    hence "x \<in> RF (TER g)"
    proof(rule contrapos_pp)
      assume x: "x \<notin> RF (TER g)"
      with w have OUT: "d_OUT g x = 0" and IN: "d_IN g x = 0" by(rule waveD_OUT wave_not_RF_IN_zero[OF g])+
      with x have "x \<notin> A \<Gamma>" "weight \<Gamma> x > 0" by(auto intro!: roofed_greaterI simp add: SAT.simps SINK.simps)
      moreover from IN d_IN_mono[of f x g, OF le] have "d_IN f x \<le> 0" by(simp)
      ultimately show "x \<notin> TER f" by(auto simp add: SAT.simps)
    qed
    moreover have "x \<notin> RF\<^sup>\<circ> (TER g)"
    proof
      assume "x \<in> RF\<^sup>\<circ> (TER g)"
      hence RF: "x \<in> RF (\<E> (TER g))" and not_E: "x \<notin> \<E> (TER g)"
        unfolding RF_essential by(simp_all add: roofed_circ_def)
      from x obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>" and distinct: "distinct (x # p)"
        and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER f)" by(rule \<E>_E_RF) blast
      from roofedD[OF RF p y] not_E obtain z where "z \<in> set p" "z \<in> \<E> (TER g)" by blast
      with subset bypass[of z] show False by(auto intro: roofed_greaterI)
    qed
    ultimately show "x \<in> \<E> (TER g)" by(simp add: roofed_circ_def)
  qed
qed

subsection \<open>Hindrances and looseness\<close>

inductive hindrance_by :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> ennreal \<Rightarrow> bool"
  for \<Gamma> (structure) and f and \<epsilon>
where
  hindrance_by:
  "\<lbrakk> a \<in> A \<Gamma>; a \<notin> \<E> (TER f); d_OUT f a < weight \<Gamma> a; \<epsilon> < weight \<Gamma> a - d_OUT f a \<rbrakk> \<Longrightarrow> hindrance_by \<Gamma> f \<epsilon>"

inductive hindrance :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> bool"
  for \<Gamma> (structure) and f
where
  hindrance:
  "\<lbrakk> a \<in> A \<Gamma>; a \<notin> \<E> (TER f); d_OUT f a < weight \<Gamma> a \<rbrakk> \<Longrightarrow> hindrance \<Gamma> f"

inductive hindered :: "('v, 'more) web_scheme \<Rightarrow> bool"
  for \<Gamma> (structure)
where hindered: "\<lbrakk> hindrance \<Gamma> f; current \<Gamma> f; wave \<Gamma> f \<rbrakk> \<Longrightarrow> hindered \<Gamma>"

inductive hindered_by :: "('v, 'more) web_scheme \<Rightarrow> ennreal \<Rightarrow> bool"
  for \<Gamma> (structure) and \<epsilon>
where hindered_by: "\<lbrakk> hindrance_by \<Gamma> f \<epsilon>; current \<Gamma> f; wave \<Gamma> f \<rbrakk> \<Longrightarrow> hindered_by \<Gamma> \<epsilon>"

lemma hindrance_into_hindrance_by:
  assumes "hindrance \<Gamma> f"
  shows "\<exists>\<epsilon>>0. hindrance_by \<Gamma> f \<epsilon>"
using assms
proof cases
  case (hindrance a)
  let ?\<epsilon> = "if weight \<Gamma> a = \<top> then 1 else (weight \<Gamma> a - d_OUT f a) / 2"
  from \<open>d_OUT f a < weight \<Gamma> a\<close> have "weight \<Gamma> a - d_OUT f a > 0" "weight \<Gamma> a \<noteq> \<top> \<Longrightarrow> weight \<Gamma> a - d_OUT f a < \<top>"
    by(simp_all add: diff_gr0_ennreal less_top diff_less_top_ennreal)
  from ennreal_mult_strict_left_mono[of 1 2, OF _ this]
  have "0 < ?\<epsilon>" and "?\<epsilon> < weight \<Gamma> a - d_OUT f a" using \<open>d_OUT f a < weight \<Gamma> a\<close>
    by(auto intro!: diff_gr0_ennreal simp: ennreal_zero_less_divide divide_less_ennreal)
  with hindrance show ?thesis by(auto intro!: hindrance_by.intros)
qed

lemma hindrance_by_into_hindrance: "hindrance_by \<Gamma> f \<epsilon> \<Longrightarrow> hindrance \<Gamma> f"
by(blast elim: hindrance_by.cases intro: hindrance.intros)

lemma hindrance_conv_hindrance_by: "hindrance \<Gamma> f \<longleftrightarrow> (\<exists>\<epsilon>>0. hindrance_by \<Gamma> f \<epsilon>)"
by(blast intro: hindrance_into_hindrance_by hindrance_by_into_hindrance)

lemma hindered_into_hindered_by: "hindered \<Gamma> \<Longrightarrow> \<exists>\<epsilon>>0. hindered_by \<Gamma> \<epsilon>"
by(blast intro: hindered_by.intros elim: hindered.cases dest: hindrance_into_hindrance_by)

lemma hindered_by_into_hindered: "hindered_by \<Gamma> \<epsilon> \<Longrightarrow> hindered \<Gamma>"
by(blast elim: hindered_by.cases intro: hindered.intros dest: hindrance_by_into_hindrance)

lemma hindered_conv_hindered_by: "hindered \<Gamma> \<longleftrightarrow> (\<exists>\<epsilon>>0. hindered_by \<Gamma> \<epsilon>)"
by(blast intro: hindered_into_hindered_by hindered_by_into_hindered)

inductive loose :: "('v, 'more) web_scheme \<Rightarrow> bool"
  for \<Gamma>
where
  loose: "\<lbrakk> \<And>f. \<lbrakk> current \<Gamma> f; wave \<Gamma> f \<rbrakk> \<Longrightarrow> f = zero_current; \<not> hindrance \<Gamma> zero_current \<rbrakk>
  \<Longrightarrow> loose \<Gamma>"

lemma looseD_hindrance: "loose \<Gamma> \<Longrightarrow> \<not> hindrance \<Gamma> zero_current"
by(simp add: loose.simps)

lemma looseD_wave:
  "\<lbrakk> loose \<Gamma>; current \<Gamma> f; wave \<Gamma> f \<rbrakk> \<Longrightarrow> f = zero_current"
by(simp add: loose.simps)

lemma loose_unhindered:
  fixes \<Gamma> (structure)
  assumes "loose \<Gamma>"
  shows "\<not> hindered \<Gamma>"
apply auto
  apply(erule hindered.cases)
apply(frule (1) looseD_wave[OF assms])
apply simp
using looseD_hindrance[OF assms]
by simp

context
  fixes \<Gamma> \<Gamma>' :: "('v, 'more) web_scheme"
  assumes [simp]: "edge \<Gamma> = edge \<Gamma>'" "A \<Gamma> = A \<Gamma>'" "B \<Gamma> = B \<Gamma>'"
  and weight_eq: "\<And>x. x \<notin> A \<Gamma>' \<Longrightarrow> weight \<Gamma> x = weight \<Gamma>' x"
  and weight_le: "\<And>a. a \<in> A \<Gamma>' \<Longrightarrow> weight \<Gamma> a \<ge> weight \<Gamma>' a"
begin

private lemma essential_eq: "essential \<Gamma> = essential \<Gamma>'"
by(simp add: fun_eq_iff essential_def)

qualified lemma TER_eq: "TER\<^bsub>\<Gamma>\<^esub> f = TER\<^bsub>\<Gamma>'\<^esub> f"
apply(auto simp add: SINK.simps SAT.simps)
apply(erule contrapos_np; drule weight_eq; simp)+
done

qualified lemma separating_eq: "separating_gen \<Gamma> = separating_gen \<Gamma>'"
by(intro ext iffI; rule separating_gen.intros; drule separatingD; simp)

qualified lemma roofed_eq: "\<And>B. roofed_gen \<Gamma> B S = roofed_gen \<Gamma>' B S"
by(simp add: roofed_def)

lemma wave_eq_web: \<comment> \<open>Observation 4.6\<close>
  "wave \<Gamma> f \<longleftrightarrow> wave \<Gamma>' f"
by(simp add: wave.simps separating_eq TER_eq roofed_eq)

lemma current_mono_web: "current \<Gamma>' f \<Longrightarrow> current \<Gamma> f"
apply(rule current, simp_all add: currentD_OUT_IN currentD_IN currentD_OUT  currentD_outside')
subgoal for x by(cases "x \<in> A \<Gamma>'")(auto dest!: weight_eq weight_le dest: currentD_weight_OUT intro: order_trans)
subgoal for x by(cases "x \<in> A \<Gamma>'")(auto dest!: weight_eq weight_le dest: currentD_weight_IN intro: order_trans)
done

lemma hindrance_mono_web: "hindrance \<Gamma>' f \<Longrightarrow> hindrance \<Gamma> f"
apply(erule hindrance.cases)
apply(rule hindrance)
  apply simp
 apply(unfold TER_eq, simp add: essential_eq)
apply(auto dest!: weight_le)
done

lemma hindered_mono_web: "hindered \<Gamma>' \<Longrightarrow> hindered \<Gamma>"
apply(erule hindered.cases)
apply(rule hindered.intros)
  apply(erule hindrance_mono_web)
 apply(erule current_mono_web)
apply(simp add: wave_eq_web)
done

end

subsection \<open>Linkage\<close>

text \<open>
  The following definition of orthogonality is stronger than the original definition 3.5 in
  @{cite AharoniBergerGeorgakopoulusPerlsteinSpruessel2011JCT} in that the outflow from any
  \<open>A\<close>-vertices in the set must saturate the vertex; @{term "S \<subseteq> SAT \<Gamma> f"} is not enough.

  With the original definition of orthogonal current, the reduction from networks to webs fails because
  the induced flow need not saturate edges going out of the source. Consider the network with three
  nodes \<open>s\<close>, \<open>x\<close>, and \<open>t\<close> and edges \<open>(s, x)\<close> and \<open>(x, t)\<close> with
  capacity \<open>1\<close>. Then, the corresponding web has the vertices \<open>(s, x)\<close> and
  \<open>(x, t)\<close> and one edge from \<open>(s, x)\<close> to \<open>(x, t)\<close>. Clearly, the zero current
  @{term [source] zero_current} is a web-flow and \<open>TER zero_current = {(s, x)}\<close>, which is essential.
  Moreover, @{term [source] zero_current} and \<open>{(s, x)}\<close> are orthogonal because
  @{term [source] zero_current} trivially saturates \<open>(s, x)\<close> as this is a vertex in \<open>A\<close>.
\<close>
inductive orthogonal_current :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> 'v set \<Rightarrow> bool"
  for \<Gamma> (structure) and f S
where orthogonal_current:
  "\<lbrakk> \<And>x. \<lbrakk> x \<in> S; x \<notin> A \<Gamma> \<rbrakk> \<Longrightarrow> weight \<Gamma> x \<le> d_IN f x;
     \<And>x. \<lbrakk> x \<in> S; x \<in> A \<Gamma>; x \<notin> B \<Gamma> \<rbrakk> \<Longrightarrow> d_OUT f x = weight \<Gamma> x;
    \<And>u v. \<lbrakk> v \<in> RF S; u \<notin> RF\<^sup>\<circ> S \<rbrakk> \<Longrightarrow> f (u, v) = 0 \<rbrakk>
  \<Longrightarrow> orthogonal_current \<Gamma> f S"

lemma orthogonal_currentD_SAT: "\<lbrakk> orthogonal_current \<Gamma> f S; x \<in> S \<rbrakk> \<Longrightarrow> x \<in> SAT \<Gamma> f"
by(auto elim!: orthogonal_current.cases intro: SAT.intros)

lemma orthogonal_currentD_A: "\<lbrakk> orthogonal_current \<Gamma> f S; x \<in> S; x \<in> A \<Gamma>; x \<notin> B \<Gamma> \<rbrakk> \<Longrightarrow> d_OUT f x = weight \<Gamma> x"
by(auto elim: orthogonal_current.cases)

lemma orthogonal_currentD_in: "\<lbrakk> orthogonal_current \<Gamma> f S; v \<in> RF\<^bsub>\<Gamma>\<^esub> S; u \<notin> RF\<^sup>\<circ>\<^bsub>\<Gamma>\<^esub> S \<rbrakk> \<Longrightarrow> f (u, v) = 0"
by(auto elim: orthogonal_current.cases)

inductive linkage :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> bool"
  for \<Gamma> f
where \<comment> \<open>Omit the condition @{const web_flow}\<close>
  linkage: "(\<And>x. x \<in> A \<Gamma> \<Longrightarrow> d_OUT f x = weight \<Gamma> x) \<Longrightarrow> linkage \<Gamma> f"

lemma linkageD: "\<lbrakk> linkage \<Gamma> f; x \<in> A \<Gamma> \<rbrakk> \<Longrightarrow> d_OUT f x = weight \<Gamma> x"
by(rule linkage.cases)

abbreviation linkable :: "('v, 'more) web_scheme \<Rightarrow> bool"
where "linkable \<Gamma> \<equiv> \<exists>f. web_flow \<Gamma> f \<and> linkage \<Gamma> f"

subsection \<open>Trimming\<close>

context
  fixes \<Gamma> :: "('v, 'more) web_scheme" (structure)
  and f :: "'v current"
begin

inductive trimming :: "'v current \<Rightarrow> bool"
  for g
where
  trimming:
  \<comment> \<open>omits the condition that @{term f} is a wave\<close>
  "\<lbrakk> current \<Gamma> g; wave \<Gamma> g; g \<le> f; \<And>x. \<lbrakk> x \<in> RF\<^sup>\<circ> (TER f); x \<notin> A \<Gamma> \<rbrakk> \<Longrightarrow> KIR g x; \<E> (TER g) - A \<Gamma> = \<E> (TER f) - A \<Gamma> \<rbrakk>
  \<Longrightarrow> trimming g"

lemma assumes "trimming g"
  shows trimmingD_current: "current \<Gamma> g"
  and trimmingD_wave: "wave \<Gamma> g"
  and trimmingD_le: "\<And>e. g e \<le> f e"
  and trimmingD_KIR: "\<lbrakk> x \<in> RF\<^sup>\<circ> (TER f); x \<notin> A \<Gamma> \<rbrakk> \<Longrightarrow> KIR g x"
  and trimmingD_\<E>: "\<E> (TER g) - A \<Gamma> = \<E> (TER f) - A \<Gamma>"
using assms by(blast elim: trimming.cases dest: le_funD)+

lemma ex_trimming: \<comment> \<open>Lemma 4.8\<close>
  assumes f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  and countable: "countable \<^bold>E"
  and weight_finite: "\<And>x. weight \<Gamma> x \<noteq> \<top>"
  shows "\<exists>g. trimming g"
proof -
  define F where "F = {g. current \<Gamma> g \<and> wave \<Gamma> g \<and> g \<le> f \<and> \<E> (TER g) = \<E> (TER f)}"
  define leq where "leq = restrict_rel F {(g, g'). g' \<le> g}"
  have in_F [simp]: "g \<in> F \<longleftrightarrow> current \<Gamma> g \<and> wave \<Gamma> g \<and> (\<forall>e. g e \<le> f e) \<and> \<E> (TER g) = \<E> (TER f)" for g
    by(simp add: F_def le_fun_def)

  have f_finite [simp]: "f e \<noteq> \<top>" for e
  proof(cases e)
    case (Pair x y)
    have "f (x, y) \<le> d_IN f y" by (rule d_IN_ge_point)
    also have "\<dots> \<le> weight \<Gamma> y" by(rule currentD_weight_IN[OF f])
    also have "\<dots> < \<top>" by(simp add: weight_finite less_top[symmetric])
    finally show ?thesis using Pair by simp
  qed

  have chainD: "Inf M \<in> F" if M: "M \<in> Chains leq" and nempty: "M \<noteq> {}" for M
  proof -
    from nempty obtain g0 where g0: "g0 \<in> M" by auto
    have g0_le_f: "g0 e \<le> f e" and g: "current \<Gamma> g0" and w0: "wave \<Gamma> g0" for e
      using Chains_FieldD[OF M g0] by(cases e, auto simp add: leq_def)

    have finite_OUT: "d_OUT f x \<noteq> \<top>" for x using weight_finite[of x]
      by(rule neq_top_trans)(rule currentD_weight_OUT[OF f])
    have finite_IN: "d_IN f x \<noteq> \<top>" for x using weight_finite[of x]
      by(rule neq_top_trans)(rule currentD_weight_IN[OF f])

    from M have "M \<in> Chains {(g, g'). g' \<le> g}"
      by(rule mono_Chains[THEN subsetD, rotated])(auto simp add: leq_def in_restrict_rel_iff)
    then have chain: "Complete_Partial_Order.chain (\<ge>) M" by(rule Chains_into_chain)
    hence chain': "Complete_Partial_Order.chain (\<le>) M" by(simp add: chain_dual)

    have countable': "countable (support_flow f)"
      using current_support_flow[OF f] by(rule countable_subset)(rule countable)

    have OUT_M: "d_OUT (Inf M) x = (INF g\<in>M. d_OUT g x)" for x using chain' nempty countable' _ finite_OUT
      by(rule d_OUT_Inf)(auto dest!: Chains_FieldD[OF M]  simp add: leq_def)
    have IN_M: "d_IN (Inf M) x = (INF g\<in>M. d_IN g x)" for x using chain' nempty countable' _ finite_IN
      by(rule d_IN_Inf)(auto dest!: Chains_FieldD[OF M]  simp add: leq_def)

    have c: "current \<Gamma> (Inf M)" using g
    proof(rule current_leI)
      show "(Inf M) e \<le> g0 e" for e using g0 by(auto intro: INF_lower)
      show "d_OUT (\<Sqinter>M) x \<le> d_IN (\<Sqinter>M) x" if "x \<notin> A \<Gamma>" for x
        by(auto 4 4 simp add: IN_M OUT_M leq_def intro!: INF_mono dest: Chains_FieldD[OF M] intro: currentD_OUT_IN[OF _ that])
    qed

    have INF_le_f: "Inf M e \<le> f e" for e using g0 by(auto intro!: INF_lower2 g0_le_f)
    have eq: "\<E> (TER (Inf M)) = \<E> (TER f)" using f w INF_le_f
    proof(rule essential_eq_leI; intro subsetI)
      fix x
      assume x: "x \<in> \<E> (TER f)"
      hence "x \<in> SINK (Inf M)" using d_OUT_mono[of "Inf M" x f, OF INF_le_f]
        by(auto simp add: SINK.simps)
      moreover from x have "x \<in> SAT \<Gamma> g" if "g \<in> M" for g using Chains_FieldD[OF M that] by(auto simp add: leq_def)
      hence "x \<in> SAT \<Gamma> (Inf M)" by(auto simp add: SAT.simps IN_M intro!: INF_greatest)
      ultimately show "x \<in> TER (Inf M)" by auto
    qed

    have w': "wave \<Gamma> (Inf M)"
    proof
      have "separating \<Gamma> (\<E> (TER f))" by(rule separating_essential)(rule waveD_separating[OF w])
      then show "separating \<Gamma> (TER (Inf M))" unfolding eq[symmetric] by(rule separating_weakening) auto

      fix x
      assume "x \<notin> RF (TER (Inf M))"
      hence "x \<notin> RF (\<E> (TER (Inf M)))" unfolding RF_essential .
      hence "x \<notin> RF (TER f)" unfolding eq RF_essential .
      hence "d_OUT f x = 0" by(rule waveD_OUT[OF w])
      with d_OUT_mono[of _ x f, OF INF_le_f]
      show "d_OUT (Inf M) x = 0" by (metis le_zero_eq)
    qed
    from c w' INF_le_f eq show ?thesis by simp
  qed

  define trim1
    where "trim1 g =
      (if trimming g then g
        else let z = SOME z. z \<in> RF\<^sup>\<circ> (TER g) \<and> z \<notin> A \<Gamma> \<and> \<not> KIR g z;
            factor = d_OUT g z / d_IN g z
          in (\<lambda>(y, x). (if x = z then factor else 1) * g (y, x)))" for g

  have increasing: "trim1 g \<le> g \<and> trim1 g \<in> F" if "g \<in> F" for g
  proof(cases "trimming g")
    case True
    thus ?thesis using that by(simp add: trim1_def)
  next
    case False
    let ?P = "\<lambda>z. z \<in> RF\<^sup>\<circ> (TER g) \<and> z \<notin> A \<Gamma> \<and> \<not> KIR g z"
    define z where "z = Eps ?P"
    from that have g: "current \<Gamma> g" and w': "wave \<Gamma> g" and le_f: "\<And>e. g e \<le> f e"
      and \<E>: "\<E> (TER g) = \<E> (TER f)" by(auto simp add: le_fun_def)
    { with False obtain z where z: "z \<in> RF\<^sup>\<circ> (TER f)" and A: "z \<notin> A \<Gamma>" and neq: "d_OUT g z \<noteq> d_IN g z"
        by(auto simp add: trimming.simps le_fun_def)
      from z have "z \<in> RF\<^sup>\<circ> (\<E> (TER f))" unfolding roofed_circ_essential .
      with \<E> roofed_circ_essential[of \<Gamma> "TER g"] have "z \<in> RF\<^sup>\<circ> (TER g)" by simp
      with A neq have "\<exists>x. ?P x" by auto }
    hence "?P z" unfolding z_def by(rule someI_ex)
    hence RF: "z \<in> RF\<^sup>\<circ> (TER g)" and A: "z \<notin> A \<Gamma>" and neq: "d_OUT g z \<noteq> d_IN g z" by simp_all
    let ?factor = "d_OUT g z / d_IN g z"
    have trim1 [simp]: "trim1 g (y, x) = (if x = z then ?factor else 1) * g (y, x)" for x y
      using False by(auto simp add: trim1_def z_def Let_def)

    from currentD_OUT_IN[OF g A] neq have less: "d_OUT g z < d_IN g z" by auto
    hence "?factor \<le> 1" (is "?factor \<le> _")
      by (auto intro!: divide_le_posI_ennreal simp: zero_less_iff_neq_zero)
    hence le': "?factor * g (y, x) \<le> 1 * g (y, x)" for y x
      by(rule mult_right_mono) simp
    hence le: "trim1 g e \<le> g e" for e by(cases e)simp
    moreover {
      have c: "current \<Gamma> (trim1 g)" using g le
      proof(rule current_leI)
        fix x
        assume x: "x \<notin> A \<Gamma>"
        have "d_OUT (trim1 g) x \<le> d_OUT g x" unfolding d_OUT_def using le' by(auto intro: nn_integral_mono)
        also have "\<dots> \<le> d_IN (trim1 g) x"
        proof(cases "x = z")
          case True
          have "d_OUT g x = d_IN (trim1 g) x" unfolding d_IN_def
            using True currentD_weight_IN[OF g, of x] currentD_OUT_IN[OF g x]
            apply (cases "d_IN g x = 0")
            apply(auto simp add: nn_integral_divide nn_integral_cmult d_IN_def[symmetric] ennreal_divide_times)
            apply (subst ennreal_divide_self)
            apply (auto simp: less_top[symmetric] top_unique weight_finite)
            done
          thus ?thesis by simp
        next
          case False
          have "d_OUT g x \<le> d_IN g x" using x by(rule currentD_OUT_IN[OF g])
          also have "\<dots> \<le> d_IN (trim1 g) x" unfolding d_IN_def using False by(auto intro!: nn_integral_mono)
          finally show ?thesis .
        qed
        finally show "d_OUT (trim1 g) x \<le> d_IN (trim1 g) x" .
      qed
      moreover have le_f: "trim1 g \<le> f" using le le_f by(blast intro: le_funI order_trans)
      moreover have eq: "\<E> (TER (trim1 g)) = \<E> (TER f)" unfolding \<E>[symmetric] using g w' le
      proof(rule essential_eq_leI; intro subsetI)
        fix x
        assume x: "x \<in> \<E> (TER g)"
        hence "x \<in> SINK (trim1 g)" using d_OUT_mono[of "trim1 g" x g, OF le]
          by(auto simp add: SINK.simps)
        moreover from x have "x \<noteq> z" using RF by(auto simp add: roofed_circ_def)
        hence "d_IN (trim1 g) x = d_IN g x" unfolding d_IN_def by simp
        with \<open>x \<in> \<E> (TER g)\<close> have "x \<in> SAT \<Gamma> (trim1 g)" by(auto simp add: SAT.simps)
        ultimately show "x \<in> TER (trim1 g)" by auto
      qed
      moreover have "wave \<Gamma> (trim1 g)"
      proof
        have "separating \<Gamma> (\<E> (TER f))" by(rule separating_essential)(rule waveD_separating[OF w])
        then show "separating \<Gamma> (TER (trim1 g))" unfolding eq[symmetric] by(rule separating_weakening) auto

        fix x
        assume "x \<notin> RF (TER (trim1 g))"
        hence "x \<notin> RF (\<E> (TER (trim1 g)))" unfolding RF_essential .
        hence "x \<notin> RF (TER f)" unfolding eq RF_essential .
        hence "d_OUT f x = 0" by(rule waveD_OUT[OF w])
        with d_OUT_mono[of _ x f, OF le_f[THEN le_funD]]
        show "d_OUT (trim1 g) x = 0" by (metis le_zero_eq)
      qed
      ultimately have "trim1 g \<in> F" by(simp add: F_def) }
    ultimately show ?thesis using that by(simp add: le_fun_def del: trim1)
  qed

  have "bourbaki_witt_fixpoint Inf leq trim1" using chainD increasing unfolding leq_def
    by(intro bourbaki_witt_fixpoint_restrict_rel)(auto intro: Inf_greatest Inf_lower)
  then interpret bourbaki_witt_fixpoint Inf leq trim1 .

  have f_Field: "f \<in> Field leq" using f w by(simp add: leq_def)

  define g where "g = fixp_above f"

  have "g \<in> Field leq" using f_Field unfolding g_def by(rule fixp_above_Field)
  hence le_f: "g \<le> f"
    and g: "current \<Gamma> g"
    and w': "wave \<Gamma> g"
    and TER: "\<E> (TER g) = \<E> (TER f)" by(auto simp add: leq_def intro: le_funI)

  have "trimming g"
  proof(rule ccontr)
    let ?P = "\<lambda>x. x \<in> RF\<^sup>\<circ> (TER g) \<and> x \<notin> A \<Gamma> \<and> \<not> KIR g x"
    define x where "x = Eps ?P"
    assume False: "\<not> ?thesis"
    hence "\<exists>x. ?P x" using le_f g w' TER
      by(auto simp add: trimming.simps roofed_circ_essential[of \<Gamma> "TER g", symmetric] roofed_circ_essential[of \<Gamma> "TER f", symmetric])
    hence "?P x" unfolding x_def by(rule someI_ex)
    hence x: "x \<in> RF\<^sup>\<circ> (TER g)" and A: "x \<notin> A \<Gamma>" and neq: "d_OUT g x \<noteq> d_IN g x" by simp_all
    from neq have "\<exists>y. edge \<Gamma> y x \<and> g (y, x) > 0"
    proof(rule contrapos_np)
      assume "\<not> ?thesis"
      hence "d_IN g x = 0" using currentD_outside[OF g, of _ x]
        by(force simp add: d_IN_def nn_integral_0_iff_AE AE_count_space not_less)
      with currentD_OUT_IN[OF g A] show "KIR g x" by simp
    qed
    then obtain y where y: "edge \<Gamma> y x" and gr0: "g (y, x) > 0" by blast

    have [simp]: "g (y, x) \<noteq> \<top>"
    proof -
      have "g (y, x) \<le> d_OUT g y" by (rule d_OUT_ge_point)
      also have "\<dots> \<le> weight \<Gamma> y" by(rule currentD_weight_OUT[OF g])
      also have "\<dots> < \<top>" by(simp add: weight_finite less_top[symmetric])
      finally show ?thesis by simp
    qed

    from neq have factor: "d_OUT g x / d_IN g x \<noteq> 1"
      by (simp add: divide_eq_1_ennreal)

    have "trim1 g (y, x) = g (y, x) * (d_OUT g x / d_IN g x)"
      by(clarsimp simp add: False trim1_def Let_def x_def[symmetric] mult.commute)
    moreover have "\<dots> \<noteq> g (y, x) * 1" unfolding ennreal_mult_cancel_left using gr0 factor by auto
    ultimately have "trim1 g (y, x) \<noteq> g (y, x)" by auto
    hence "trim1 g \<noteq> g" by(auto simp add: fun_eq_iff)
    moreover have "trim1 g = g" using f_Field unfolding g_def by(rule fixp_above_unfold[symmetric])
    ultimately show False by contradiction
  qed
  then show ?thesis by blast
qed

end

lemma trimming_\<E>:
  fixes \<Gamma> (structure)
  assumes w: "wave \<Gamma> f" and trimming: "trimming \<Gamma> f g"
  shows "\<E> (TER f) = \<E> (TER g)"
proof(rule set_eqI)
  show "x \<in> \<E> (TER f) \<longleftrightarrow> x \<in> \<E> (TER g)" for x
  proof(cases "x \<in> A \<Gamma>")
    case False
    thus ?thesis using trimmingD_\<E>[OF trimming] by blast
  next
    case True
    show ?thesis
    proof
      assume x: "x \<in> \<E> (TER f)"
      hence "x \<in> TER g" using d_OUT_mono[of g x f, OF trimmingD_le[OF trimming]] True
        by(simp add: SINK.simps SAT.A)
      moreover from x have "essential \<Gamma> (B \<Gamma>) (TER f) x" by simp
      then obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
        and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER f)" by(rule essentialE_RF) blast
      from p y have "essential \<Gamma> (B \<Gamma>) (\<E> (TER g)) x"
      proof(rule essentialI)
        fix z
        assume "z \<in> set p"
        hence z: "z \<notin> RF (TER f)" by(rule bypass)
        with waveD_separating[OF w, THEN separating_RF_A] have "z \<notin> A \<Gamma>" by blast
        with z have "z \<notin> \<E> (TER g)" using trimmingD_\<E>[OF trimming] by(auto intro: roofed_greaterI)
        thus "z = x \<or> z \<notin> \<E> (TER g)" ..
      qed
      ultimately show "x \<in> \<E> (TER g)" unfolding essential_\<E> by simp
    next
      assume "x \<in> \<E> (TER g)"
      then obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
        and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER g)" by(rule \<E>_E_RF) blast
      have z: "z \<notin> \<E> (TER f)" if "z \<in> set p" for z
      proof -
        from that have z: "z \<notin> RF (TER g)" by(rule bypass)
        with waveD_separating[OF trimmingD_wave[OF trimming], THEN separating_RF_A] have "z \<notin> A \<Gamma>" by blast
        with z show "z \<notin> \<E> (TER f)" using trimmingD_\<E>[OF trimming] by(auto intro: roofed_greaterI)
      qed
      then have "essential \<Gamma> (B \<Gamma>) (\<E> (TER f)) x" by(intro essentialI[OF p y]) auto
      moreover have "x \<in> TER f"
        using waveD_separating[THEN separating_essential, THEN separatingD, OF w p True y] z
        by auto
      ultimately show "x \<in> \<E> (TER f)" unfolding essential_\<E> by simp
    qed
  qed
qed

subsection \<open>Composition of waves via quotients\<close>

definition quotient_web :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> ('v, 'more) web_scheme"
where \<comment> \<open>Modifications to original Definition 4.9: No incoming edges to nodes in @{const A},
  @{term "B \<Gamma> - A \<Gamma>"} is not part of @{const A} such that @{const A} contains only vertices
  is disjoint from @{const B}. The weight of vertices in @{const B} saturated by @{term f} is
  therefore set to @{term "0 :: ennreal"}.\<close>
  "quotient_web \<Gamma> f =
   \<lparr>edge = \<lambda>x y. edge \<Gamma> x y \<and> x \<notin> roofed_circ \<Gamma> (TER\<^bsub>\<Gamma>\<^esub> f) \<and> y \<notin> roofed \<Gamma> (TER\<^bsub>\<Gamma>\<^esub> f),
    weight = \<lambda>x. if x \<in> RF\<^sup>\<circ>\<^bsub>\<Gamma>\<^esub> (TER\<^bsub>\<Gamma>\<^esub> f) \<or> x \<in> TER\<^bsub>\<Gamma>\<^esub> f \<inter> B \<Gamma> then 0 else weight \<Gamma> x,
    A = \<E>\<^bsub>\<Gamma>\<^esub> (TER\<^bsub>\<Gamma>\<^esub> f) - (B \<Gamma> - A \<Gamma>),
    B = B \<Gamma>,
    \<dots> = web.more \<Gamma>\<rparr>"

lemma quotient_web_sel [simp]:
  fixes \<Gamma> (structure) shows
  "edge (quotient_web \<Gamma> f) x y \<longleftrightarrow> edge \<Gamma> x y \<and> x \<notin> RF\<^sup>\<circ> (TER f) \<and> y \<notin> RF (TER f)"
  "weight (quotient_web \<Gamma> f) x = (if x \<in> RF\<^sup>\<circ> (TER f) \<or> x \<in> TER\<^bsub>\<Gamma>\<^esub> f \<inter> B \<Gamma> then 0 else weight \<Gamma> x)"
  "A (quotient_web \<Gamma> f) = \<E> (TER f)- (B \<Gamma> - A \<Gamma>)"
  "B (quotient_web \<Gamma> f) = B \<Gamma>"
  "web.more (quotient_web \<Gamma> f) = web.more \<Gamma>"
by(simp_all add: quotient_web_def)

lemma vertex_quotient_webD: fixes \<Gamma> (structure) shows
  "vertex (quotient_web \<Gamma> f) x \<Longrightarrow> vertex \<Gamma> x \<and> x \<notin> RF\<^sup>\<circ> (TER f)"
by(auto simp add: vertex_def roofed_circ_def)

lemma path_quotient_web:
  fixes \<Gamma> (structure)
  assumes "path \<Gamma> x p y"
  and "x \<notin> RF\<^sup>\<circ> (TER f)"
  and "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER f)"
  shows "path (quotient_web \<Gamma> f) x p y"
using assms by(induction)(auto intro: rtrancl_path.intros simp add: roofed_circ_def)

definition restrict_current :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> 'v current \<Rightarrow> 'v current"
where "restrict_current \<Gamma> f g = (\<lambda>(x, y). g (x, y) * indicator (- RF\<^sup>\<circ>\<^bsub>\<Gamma>\<^esub> (TER\<^bsub>\<Gamma>\<^esub> f)) x * indicator (- RF\<^bsub>\<Gamma>\<^esub> (TER\<^bsub>\<Gamma>\<^esub> f)) y)"

abbreviation restrict_curr :: "'v current \<Rightarrow> ('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> 'v current" ("_ \<upharpoonleft> _ '/ _" [100, 0, 100] 100)
where "restrict_curr g \<Gamma> f \<equiv> restrict_current \<Gamma> f g"

lemma restrict_current_simps [simp]: fixes \<Gamma> (structure) shows
  "(g \<upharpoonleft> \<Gamma> / f) (x, y) = (g (x, y) * indicator (- RF\<^sup>\<circ> (TER f)) x * indicator (- RF (TER f)) y)"
by(simp add: restrict_current_def)

lemma d_OUT_restrict_current_outside: fixes \<Gamma> (structure) shows
  "x \<in> RF\<^sup>\<circ> (TER f) \<Longrightarrow> d_OUT (g \<upharpoonleft> \<Gamma> / f) x = 0"
by(simp add: d_OUT_def)

lemma d_IN_restrict_current_outside: fixes \<Gamma> (structure) shows
  "x \<in> RF (TER f) \<Longrightarrow> d_IN (g \<upharpoonleft> \<Gamma> / f) x = 0"
by(simp add: d_IN_def)

lemma restrict_current_le: "(g \<upharpoonleft> \<Gamma> / f) e \<le> g e"
by(cases e)(clarsimp split: split_indicator)

lemma d_OUT_restrict_current_le: "d_OUT (g \<upharpoonleft> \<Gamma> / f) x \<le> d_OUT g x"
unfolding d_OUT_def by(rule nn_integral_mono, simp split: split_indicator)

lemma d_IN_restrict_current_le: "d_IN (g \<upharpoonleft> \<Gamma> / f) x \<le> d_IN g x"
unfolding d_IN_def by(rule nn_integral_mono, simp split: split_indicator)

lemma restrict_current_IN_not_RF:
  fixes \<Gamma> (structure)
  assumes g: "current \<Gamma> g"
  and x: "x \<notin> RF (TER f)"
  shows "d_IN (g \<upharpoonleft> \<Gamma> / f) x = d_IN g x"
proof -
  {
    fix y
    assume y: "y \<in> RF\<^sup>\<circ> (TER f)"
    have "g (y, x) = 0"
    proof(cases "edge \<Gamma> y x")
      case True
      from y have y': "y \<in> RF (TER f)" and essential: "y \<notin> \<E> (TER f)" by(simp_all add: roofed_circ_def)
      moreover from x obtain p z where z: "z \<in> B \<Gamma>" and p: "path \<Gamma> x p z"
        and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> TER f" "x \<notin> TER f"
        by(clarsimp simp add: roofed_def)
      from roofedD[OF y' rtrancl_path.step, OF True p z] bypass have "x \<in> TER f \<or> y \<in> TER f" by auto
      with roofed_greater[THEN subsetD, of x "TER f" \<Gamma>] x have "x \<notin> TER f" "y \<in> TER f" by auto
      with essential bypass have False
        by(auto dest!: not_essentialD[OF _ rtrancl_path.step, OF _ True p z])
      thus ?thesis ..
    qed(simp add: currentD_outside[OF g]) }
  then show ?thesis unfolding d_IN_def
    using x by(auto intro!: nn_integral_cong split: split_indicator)
qed

lemma restrict_current_IN_A:
  "a \<in> A (quotient_web \<Gamma> f) \<Longrightarrow> d_IN (g \<upharpoonleft> \<Gamma> / f) a = 0"
by(simp add: d_IN_restrict_current_outside roofed_greaterI)

lemma restrict_current_nonneg: "0 \<le> g e \<Longrightarrow> 0 \<le> (g \<upharpoonleft> \<Gamma> / f) e"
by(cases e) simp

lemma in_SINK_restrict_current: "x \<in> SINK g \<Longrightarrow> x \<in> SINK (g \<upharpoonleft> \<Gamma> / f)"
using d_OUT_restrict_current_le[of \<Gamma> f g x]
by(simp add: SINK.simps)

lemma SAT_restrict_current:
  fixes \<Gamma> (structure)
  assumes f: "current \<Gamma> f"
  and g: "current \<Gamma> g"
  shows "SAT (quotient_web \<Gamma> f) (g \<upharpoonleft> \<Gamma> / f) = RF (TER f) \<union> (SAT \<Gamma> g - A \<Gamma>)" (is "SAT ?\<Gamma> ?g = ?rhs")
proof(intro set_eqI iffI; (elim UnE DiffE)?)
  show "x \<in> ?rhs" if "x \<in> SAT ?\<Gamma> ?g" for x using that
  proof cases
    case IN
    thus ?thesis using currentD_weight_OUT[OF f, of x]
      by(cases "x \<in> RF (TER f)")(auto simp add: d_IN_restrict_current_outside roofed_circ_def restrict_current_IN_not_RF[OF g] SAT.IN currentD_IN[OF g] roofed_greaterI SAT.A SINK.simps RF_in_B split: if_split_asm intro: essentialI[OF rtrancl_path.base])
  qed(simp add: roofed_greaterI)
  show "x \<in> SAT ?\<Gamma> ?g" if "x \<in> RF (TER f)" for x using that
    by(auto simp add: SAT.simps roofed_circ_def d_IN_restrict_current_outside)
  show "x \<in> SAT ?\<Gamma> ?g" if "x \<in> SAT \<Gamma> g" "x \<notin> A \<Gamma>" for x using that
    by(auto simp add: SAT.simps roofed_circ_def d_IN_restrict_current_outside restrict_current_IN_not_RF[OF g])
qed

lemma current_restrict_current:
  fixes \<Gamma> (structure)
  assumes w: "wave \<Gamma> f"
  and g: "current \<Gamma> g"
  shows "current (quotient_web \<Gamma> f) (g \<upharpoonleft> \<Gamma> / f)" (is "current ?\<Gamma> ?g")
proof
  show "d_OUT ?g x \<le> weight ?\<Gamma> x" for x
    using d_OUT_restrict_current_le[of \<Gamma> f g x] currentD_weight_OUT[OF g, of x] currentD_OUT[OF g, of x]
    by(auto simp add: d_OUT_restrict_current_outside)
  show "d_IN ?g x \<le> weight ?\<Gamma> x" for x
    using d_IN_restrict_current_le[of \<Gamma> f g x] currentD_weight_IN[OF g, of x]
    by(auto simp add: d_IN_restrict_current_outside roofed_circ_def)
      (subst d_IN_restrict_current_outside[of x \<Gamma> f g]; simp add: roofed_greaterI)

  fix x
  assume "x \<notin> A ?\<Gamma>"
  hence x: "x \<notin> \<E> (TER f) - B \<Gamma>" by simp
  show "d_OUT ?g x \<le> d_IN ?g x"
  proof(cases "x \<in> RF (TER f)")
    case True
    with x have "x \<in> RF\<^sup>\<circ> (TER f) \<union> B \<Gamma>" by(simp add: roofed_circ_def)
    with True show ?thesis using currentD_OUT[OF g, of x] d_OUT_restrict_current_le[of \<Gamma> f g x]
      by(auto simp add: d_OUT_restrict_current_outside d_IN_restrict_current_outside)
  next
    case False
    then obtain p z where z: "z \<in> B \<Gamma>" and p: "path \<Gamma> x p z"
      and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> TER f" "x \<notin> TER f"
      by(clarsimp simp add: roofed_def)
    from g False have "d_IN ?g x = d_IN g x" by(rule restrict_current_IN_not_RF)
    moreover have "d_OUT ?g x \<le> d_OUT g x"
      by(rule d_OUT_mono restrict_current_le)+
    moreover have "x \<notin> A \<Gamma>"
      using separatingD[OF waveD_separating[OF w] p _ z] bypass by blast
    note currentD_OUT_IN[OF g this]
    ultimately show ?thesis by simp
  qed
next
  show "d_IN ?g a = 0" if "a \<in> A ?\<Gamma>" for a using that by(rule restrict_current_IN_A)
  show "d_OUT ?g b = 0" if "b \<in> B ?\<Gamma>" for b
    using d_OUT_restrict_current_le[of \<Gamma> f g b] currentD_OUT[OF g, of b] that by simp
  show "?g e = 0" if "e \<notin> \<^bold>E\<^bsub>?\<Gamma>\<^esub>" for e using that currentD_outside'[OF g, of e]
    by(cases e)(auto split: split_indicator)
qed

lemma TER_restrict_current:
  fixes \<Gamma> (structure)
  assumes f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  and g: "current \<Gamma> g"
  shows "TER g \<subseteq> TER\<^bsub>quotient_web \<Gamma> f\<^esub> (g \<upharpoonleft> \<Gamma> / f)" (is "_ \<subseteq> ?TER" is "_ \<subseteq> TER\<^bsub>?\<Gamma>\<^esub> ?g")
proof
  fix x
  assume x: "x \<in> TER g"
  hence "x \<in> SINK ?g" by(simp add: in_SINK_restrict_current)
  moreover have "x \<in> RF (TER f)" if "x \<in> A \<Gamma>"
    using waveD_separating[OF w, THEN separatingD, OF _ that] by(rule roofedI)
  then have "x \<in> SAT ?\<Gamma> ?g" using SAT_restrict_current[OF f g] x by auto
  ultimately show "x \<in> ?TER" by simp
qed

lemma wave_restrict_current:
  fixes \<Gamma> (structure)
  assumes f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  and g: "current \<Gamma> g"
  and w': "wave \<Gamma> g"
  shows "wave (quotient_web \<Gamma> f) (g \<upharpoonleft> \<Gamma> / f)" (is "wave ?\<Gamma> ?g")
proof
  show "separating ?\<Gamma> (TER\<^bsub>?\<Gamma>\<^esub> ?g)" (is "separating _ ?TER")
  proof
    fix x y p
    assume "x \<in> A ?\<Gamma>" "y \<in> B ?\<Gamma>" and p: "path ?\<Gamma> x p y"
    hence x: "x \<in> \<E> (TER f)" and y: "y \<in> B \<Gamma>" and SAT: "x \<in> SAT ?\<Gamma> ?g" by(simp_all add: SAT.A)
    from p have p': "path \<Gamma> x p y" by(rule rtrancl_path_mono) simp

    { assume "x \<notin> ?TER"
      hence "x \<notin> SINK ?g" using SAT by(simp)
      hence "x \<notin> SINK g" using d_OUT_restrict_current_le[of \<Gamma> f g x]
        by(auto simp add: SINK.simps)
      hence "x \<in> RF (TER g)" using waveD_OUT[OF w'] by(auto simp add: SINK.simps)
      from roofedD[OF this p' y] \<open>x \<notin> SINK g\<close> have "(\<exists>z\<in>set p. z \<in> ?TER)"
        using TER_restrict_current[OF f w g] by blast }
    then show "(\<exists>z\<in>set p. z \<in> ?TER) \<or> x \<in> ?TER" by blast
  qed

  fix x
  assume "x \<notin> RF\<^bsub>?\<Gamma>\<^esub> ?TER"
  hence "x \<notin> RF (TER g)"
  proof(rule contrapos_nn)
    assume *: "x \<in> RF (TER g)"
    show "x \<in> RF\<^bsub>?\<Gamma>\<^esub> ?TER"
    proof
      fix p y
      assume "path ?\<Gamma> x p y" "y \<in> B ?\<Gamma>"
      hence "path \<Gamma> x p y" "y \<in> B \<Gamma>" by(auto elim: rtrancl_path_mono)
      from roofedD[OF * this] show "(\<exists>z\<in>set p. z \<in> ?TER) \<or> x \<in> ?TER"
        using TER_restrict_current[OF f w g] by blast
    qed
  qed
  with w' have "d_OUT g x = 0" by(rule waveD_OUT)
  with d_OUT_restrict_current_le[of \<Gamma> f g x]
  show "d_OUT ?g x = 0" by simp
qed

definition plus_current :: "'v current \<Rightarrow> 'v current \<Rightarrow> 'v current"
where "plus_current f g = (\<lambda>e. f e + g e)"

lemma plus_current_simps [simp]: "plus_current f g e = f e + g e"
by(simp add: plus_current_def)

lemma plus_zero_current [simp]: "plus_current f zero_current = f"
by(simp add: fun_eq_iff)

lemma support_flow_plus_current: "support_flow (plus_current f g) \<subseteq> support_flow f \<union> support_flow g"
by(clarsimp simp add: support_flow.simps)

context
  fixes \<Gamma> :: "('v, 'more) web_scheme" (structure) and f g
  assumes f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  and g: "current (quotient_web \<Gamma> f) g"
begin

lemma OUT_plus_current: "d_OUT (plus_current f g) x = (if x \<in> RF\<^sup>\<circ> (TER f) then d_OUT f x else d_OUT g x)" (is "d_OUT ?g _ = _")
proof -
  have "d_OUT ?g x = d_OUT f x + d_OUT g x" unfolding plus_current_def
    by(subst d_OUT_add) simp_all
  also have "\<dots> = (if x \<in> RF\<^sup>\<circ> (TER f) then d_OUT f x else d_OUT g x)"
  proof(cases "x \<in> RF\<^sup>\<circ> (TER f)")
    case True
    hence "d_OUT g x = 0" by(intro currentD_outside_OUT[OF g])(auto dest: vertex_quotient_webD)
    thus ?thesis using True by simp
  next
    case False
    hence "d_OUT f x = 0" by(auto simp add: roofed_circ_def SINK.simps dest: waveD_OUT[OF w])
    with False show ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma IN_plus_current: "d_IN (plus_current f g) x = (if x \<in> RF (TER f) then d_IN f x else d_IN g x)" (is "d_IN ?g _ = _")
proof -
  have "d_IN ?g x = d_IN f x + d_IN g x" unfolding plus_current_def
    by(subst d_IN_add) simp_all
  also consider (RF) "x \<in> RF (TER f) - (B \<Gamma> - A \<Gamma>)" | (B) "x \<in> RF (TER f)" "x \<in> B \<Gamma> - A \<Gamma>" | (beyond) "x \<notin> RF (TER f)" by blast
  then have "d_IN f x + d_IN g x = (if x \<in> RF (TER f) then d_IN f x else d_IN g x)"
  proof(cases)
    case RF
    hence "d_IN g x = 0"
      by(cases "x \<in> \<E> (TER f)")(auto intro: currentD_outside_IN[OF g] currentD_IN[OF g] dest!: vertex_quotient_webD simp add: roofed_circ_def)
    thus ?thesis using RF by simp
  next
    case B
    hence "d_IN g x = 0" using currentD_outside_IN[OF g, of x] currentD_weight_IN[OF g, of x]
      by(auto dest: vertex_quotient_webD simp add: roofed_circ_def)
    with B show ?thesis by simp
  next
    case beyond
    from f w beyond have "d_IN f x = 0" by(rule wave_not_RF_IN_zero)
    with beyond show ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma in_TER_plus_current:
  assumes RF: "x \<notin> RF\<^sup>\<circ> (TER f)"
  and x: "x \<in> TER\<^bsub>quotient_web \<Gamma> f\<^esub> g" (is "_ \<in> ?TER _")
  shows "x \<in> TER (plus_current f g)"  (is "_ \<in> TER ?g")
proof(cases "x \<in> \<E> (TER f) - (B \<Gamma> - A \<Gamma>)")
  case True
  with x show ?thesis using currentD_IN[OF g, of x]
    by(fastforce intro: roofed_greaterI SAT.intros simp add: SINK.simps OUT_plus_current IN_plus_current elim!: SAT.cases)
next
  case *: False
  have "x \<in> SAT \<Gamma> ?g"
  proof(cases "x \<in> B \<Gamma> - A \<Gamma>")
    case False
    with x RF * have "weight \<Gamma> x \<le> d_IN g x"
      by(auto elim!: SAT.cases split: if_split_asm simp add: essential_BI)
    also have "\<dots> \<le> d_IN ?g x" unfolding plus_current_def by(intro d_IN_mono) simp
    finally show ?thesis ..
  next
    case True
    with * x have "weight \<Gamma> x \<le> d_IN ?g x" using currentD_OUT[OF f, of x]
      by(auto simp add: IN_plus_current RF_in_B SINK.simps roofed_circ_def elim!: SAT.cases split: if_split_asm)
    thus ?thesis ..
  qed
  moreover have "x \<in> SINK ?g" using x by(simp add: SINK.simps OUT_plus_current RF)
  ultimately show ?thesis by simp
qed

lemma current_plus_current: "current \<Gamma> (plus_current f g)" (is "current _ ?g")
proof
  show "d_OUT ?g x \<le> weight \<Gamma> x" for x
    using currentD_weight_OUT[OF g, of x] currentD_weight_OUT[OF f, of x]
    by(auto simp add: OUT_plus_current split: if_split_asm elim: order_trans)
  show "d_IN ?g x \<le> weight \<Gamma> x" for x
    using currentD_weight_IN[OF f, of x] currentD_weight_IN[OF g, of x]
    by(auto simp add: IN_plus_current roofed_circ_def split: if_split_asm elim: order_trans)
  show "d_OUT ?g x \<le> d_IN ?g x" if "x \<notin> A \<Gamma>" for x
  proof(cases "x \<in> \<E> (TER f)")
    case False
    thus ?thesis
      using currentD_OUT_IN[OF f that] currentD_OUT_IN[OF g, of x] that
      by(auto simp add: OUT_plus_current IN_plus_current roofed_circ_def SINK.simps)
  next
    case True
    with that have "d_OUT f x = 0" "weight \<Gamma> x \<le> d_IN f x"
      by(auto simp add: SINK.simps elim: SAT.cases)
    thus ?thesis using that True currentD_OUT_IN[OF g, of x] currentD_weight_OUT[OF g, of x]
      by(auto simp add: OUT_plus_current IN_plus_current roofed_circ_def intro: roofed_greaterI split: if_split_asm)
  qed
  show "d_IN ?g a = 0" if "a \<in> A \<Gamma>" for a
    using wave_A_in_RF[OF w that] currentD_IN[OF f that] by(simp add: IN_plus_current)
  show "d_OUT ?g b = 0" if "b \<in> B \<Gamma>" for b
    using that currentD_OUT[OF f that] currentD_OUT[OF g, of b] that
    by(auto simp add: OUT_plus_current SINK.simps roofed_circ_def intro: roofed_greaterI)
  show "?g e = 0" if "e \<notin> \<^bold>E" for e using currentD_outside'[OF f, of e] currentD_outside'[OF g, of e] that
    by(cases e) auto
qed

context
  assumes w': "wave (quotient_web \<Gamma> f) g"
begin

lemma separating_TER_plus_current:
  assumes x: "x \<in> RF (TER f)" and y: "y \<in> B \<Gamma>" and p: "path \<Gamma> x p y"
  shows "(\<exists>z\<in>set p. z \<in> TER (plus_current f g)) \<or> x \<in> TER (plus_current f g)" (is "_ \<or> _ \<in> TER ?g")
proof -
  from x have "x \<in> RF (\<E> (TER f))" unfolding RF_essential .
  from roofedD[OF this p y] have "\<exists>z\<in>set (x # p). z \<in> \<E> (TER f)" by auto
  from split_list_last_prop[OF this] obtain ys z zs
    where decomp: "x # p = ys @ z # zs" and z: "z \<in> \<E> (TER f)"
    and outside: "\<And>z. z \<in> set zs \<Longrightarrow> z \<notin> \<E> (TER f)" by auto
  have zs: "path \<Gamma> z zs y" using decomp p
    by(cases ys)(auto elim: rtrancl_path_appendE)
  moreover have "z \<notin> RF\<^sup>\<circ> (TER f)" using z by(simp add: roofed_circ_def)
  moreover have RF: "z' \<notin> RF (TER f)" if "z' \<in> set zs" for z'
  proof
    assume "z' \<in> RF (TER f)"
    hence z': "z' \<in> RF (\<E> (TER f))" by(simp only: RF_essential)
    from split_list[OF that] obtain ys' zs' where decomp': "zs = ys' @ z' # zs'" by blast
    with zs have "path \<Gamma> z' zs' y" by(auto elim: rtrancl_path_appendE)
    from roofedD[OF z' this y] outside decomp' show False by auto
  qed
  ultimately have p': "path (quotient_web \<Gamma> f) z zs y" by(rule path_quotient_web)
  show ?thesis
  proof(cases "z \<in> B \<Gamma> - A \<Gamma>")
    case False
    with separatingD[OF waveD_separating[OF w'] p'] z y
    obtain z' where z': "z' \<in> set (z # zs)" and TER: "z' \<in> TER\<^bsub>quotient_web \<Gamma> f\<^esub> g" by auto
    hence "z' \<in> TER ?g" using in_TER_plus_current[of z'] RF[of z'] \<open>z \<notin> RF\<^sup>\<circ> (TER f)\<close> by(auto simp add: roofed_circ_def)
    with decomp z' show ?thesis by(cases ys) auto
  next
    case True
    hence "z \<in> TER ?g" using currentD_OUT[OF current_plus_current, of z] z
      by(auto simp add: SINK.simps SAT.simps IN_plus_current intro: roofed_greaterI)
    then show ?thesis using decomp by(cases ys) auto
  qed
qed

lemma wave_plus_current: "wave \<Gamma> (plus_current f g)" (is "wave _ ?g")
proof
  let ?\<Gamma> = "quotient_web \<Gamma> f"
  let ?TER = "TER\<^bsub>?\<Gamma>\<^esub>"

  show "separating \<Gamma> (TER ?g)" using separating_TER_plus_current[OF wave_A_in_RF[OF w]] by(rule separating)

  fix x
  assume x: "x \<notin> RF (TER ?g)"
  hence "x \<notin> RF (TER f)" by(rule contrapos_nn)(rule roofedI, rule separating_TER_plus_current)
  hence *: "x \<notin> RF\<^sup>\<circ> (TER f)" by(simp add: roofed_circ_def)
  moreover have "x \<notin> RF\<^bsub>?\<Gamma>\<^esub> (?TER g)"
  proof
    assume RF': "x \<in> RF\<^bsub>?\<Gamma>\<^esub> (?TER g)"
    from x obtain p y where y: "y \<in> B \<Gamma>" and p: "path \<Gamma> x p y"
      and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> TER ?g" and x': "x \<notin> TER ?g"
      by(auto simp add: roofed_def)
    have RF: "z \<notin> RF (TER f)" if "z \<in> set p" for z
    proof
      assume z: "z \<in> RF (TER f)"
      from split_list[OF that] obtain ys' zs' where decomp: "p = ys' @ z # zs'" by blast
      with p have "path \<Gamma> z zs' y" by(auto elim: rtrancl_path_appendE)
      from separating_TER_plus_current[OF z y this] decomp bypass show False by auto
    qed
    with p have "path ?\<Gamma> x p y" using *
      by(induction)(auto intro: rtrancl_path.intros simp add: roofed_circ_def)
    from roofedD[OF RF' this] y consider (x) "x \<in> ?TER g" | (z) z where "z \<in> set p" "z \<in> ?TER g" by auto
    then show False
    proof(cases)
      case x
      with * have "x \<in> TER ?g" by(rule in_TER_plus_current)
      with x' show False by contradiction
    next
      case (z z)
      from z(1) have "z \<notin> RF (TER f)" by(rule RF)
      hence "z \<notin> RF\<^sup>\<circ> (TER f)" by(simp add: roofed_circ_def)
      hence "z \<in> TER ?g" using z(2) by(rule in_TER_plus_current)
      moreover from z(1) have "z \<notin> TER ?g" by(rule bypass)
      ultimately show False by contradiction
    qed
  qed
  with w' have "d_OUT g x = 0" by(rule waveD_OUT)
  ultimately show "d_OUT ?g x = 0" by(simp add: OUT_plus_current)
qed

end

end

lemma loose_quotient_web:
  fixes \<Gamma> :: "('v, 'more) web_scheme" (structure)
  assumes weight_finite: "\<And>x. weight \<Gamma> x \<noteq> \<top>"
  and f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  and maximal: "\<And>w. \<lbrakk> current \<Gamma> w; wave \<Gamma> w; f \<le> w \<rbrakk> \<Longrightarrow> f = w"
  shows "loose (quotient_web \<Gamma> f)" (is "loose ?\<Gamma>")
proof
  fix g
  assume g: "current ?\<Gamma> g" and w': "wave ?\<Gamma> g"
  let ?g = "plus_current f g"
  from f w g have "current \<Gamma> ?g" "wave \<Gamma> ?g" by(rule current_plus_current wave_plus_current)+ (rule w')
  moreover have "f \<le> ?g" by(clarsimp simp add: le_fun_def add_eq_0_iff_both_eq_0)
  ultimately have eq: "f = ?g" by(rule maximal)
  have "g e = 0" for e
  proof(cases e)
    case (Pair x y)
    have "f e \<le> d_OUT f x" unfolding Pair by (rule d_OUT_ge_point)
    also have "\<dots> \<le> weight \<Gamma> x" by(rule currentD_weight_OUT[OF f])
    also have "\<dots> < \<top>" by(simp add: weight_finite less_top[symmetric])
    finally show "g e = 0" using Pair eq[THEN fun_cong, of e]
      by(cases "f e" "g e" rule: ennreal2_cases)(simp_all add: fun_eq_iff)
  qed
  thus "g = (\<lambda>_. 0)" by(simp add: fun_eq_iff)
next
  have 0: "current ?\<Gamma> zero_current" by(simp add: )
  show "\<not> hindrance ?\<Gamma> zero_current"
  proof
    assume "hindrance ?\<Gamma> zero_current"
    then obtain x where a: "x \<in> A ?\<Gamma>" and \<E>: "x \<notin> \<E>\<^bsub>?\<Gamma>\<^esub> (TER\<^bsub>?\<Gamma>\<^esub> zero_current)"
      and "d_OUT zero_current x < weight ?\<Gamma> x" by cases
    from a have "x \<in> \<E> (TER f)" by simp
    then obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
      and bypass: "\<And>z. \<lbrakk>x \<noteq> y; z \<in> set p\<rbrakk> \<Longrightarrow> z = x \<or> z \<notin> TER f" by(rule \<E>_E) blast
    from p obtain p' where p': "path \<Gamma> x p' y" and distinct: "distinct (x # p')"
      and subset: "set p' \<subseteq> set p" by(auto elim: rtrancl_path_distinct)
    note p'
    moreover have RF: "z \<notin> RF (TER f)" if "z \<in> set p'" for z
    proof
      assume z: "z \<in> RF (TER f)"
      from split_list[OF that] obtain ys zs where decomp: "p' = ys @ z # zs" by blast
      with p' have "y \<in> set p'" by(auto dest!: rtrancl_path_last intro: last_in_set)
      with distinct have neq: "x \<noteq> y" by auto
      from decomp p' have "path \<Gamma> z zs y" by(auto elim: rtrancl_path_appendE)
      from roofedD[OF z this y] obtain z' where "z' \<in> set (z # zs)" "z' \<in> TER f" by auto
      with distinct decomp subset bypass[OF neq] show False by auto
    qed
    moreover have "x \<notin> RF\<^sup>\<circ> (TER f)" using \<open>x \<in> \<E> (TER f)\<close> by(simp add: roofed_circ_def)
    ultimately have p'': "path ?\<Gamma> x p' y"
      by(induction)(auto intro: rtrancl_path.intros simp add: roofed_circ_def)
    from a \<E> have "\<not> essential ?\<Gamma> (B ?\<Gamma>) (TER\<^bsub>?\<Gamma>\<^esub> zero_current) x" by simp
    from not_essentialD[OF this p''] y obtain z where neq: "x \<noteq> y"
      and "z \<in> set p'" "z \<noteq> x" "z \<in> TER\<^bsub>?\<Gamma>\<^esub> zero_current" by auto
    moreover with subset RF[of z] have "z \<in> TER f"
      using currentD_weight_OUT[OF f, of z] currentD_weight_IN[OF f, of z]
      by(auto simp add: roofed_circ_def SINK.simps intro: SAT.IN split: if_split_asm)
    ultimately show False using bypass[of z] subset by auto
  qed
qed

lemma quotient_web_trimming:
  fixes \<Gamma> (structure)
  assumes w: "wave \<Gamma> f"
  and trimming: "trimming \<Gamma> f g"
  shows "quotient_web \<Gamma> f = quotient_web \<Gamma> g" (is "?lhs = ?rhs")
proof(rule web.equality)
  from trimming have \<E>: "\<E> (TER g) - A \<Gamma> = \<E> (TER f) - A \<Gamma>" by cases

  have RF: "RF (TER g) = RF (TER f)"
    by(subst (1 2) RF_essential[symmetric])(simp only: trimming_\<E>[OF w trimming])
  have RFc: "RF\<^sup>\<circ> (TER g) = RF\<^sup>\<circ> (TER f)"
    by(subst (1 2) roofed_circ_essential[symmetric])(simp only: trimming_\<E>[OF w trimming])

  show "edge ?lhs = edge ?rhs" by(rule ext)+(simp add: RF RFc)
  have "weight ?lhs = (\<lambda>x. if x \<in> RF\<^sup>\<circ> (TER g) \<or> x \<in> RF (TER g) \<inter> B \<Gamma> then 0 else weight \<Gamma> x)"
    unfolding RF RFc by(auto simp add: fun_eq_iff RF_in_B)
  also have "\<dots> = weight ?rhs" by(auto simp add: fun_eq_iff RF_in_B)
  finally show "weight ?lhs = weight ?rhs" .

  show "A ?lhs = A ?rhs" unfolding quotient_web_sel trimming_\<E>[OF w trimming] ..
qed simp_all

subsection \<open>Well-formed webs\<close>

locale web =
  fixes \<Gamma> :: "('v, 'more) web_scheme" (structure)
  assumes A_in: "x \<in> A \<Gamma> \<Longrightarrow> \<not> edge \<Gamma> y x"
  and B_out: "x \<in> B \<Gamma> \<Longrightarrow> \<not> edge \<Gamma> x y"
  and A_vertex: "A \<Gamma> \<subseteq> \<^bold>V"
  and disjoint: "A \<Gamma> \<inter> B \<Gamma> = {}"
  and no_loop: "\<And>x. \<not> edge \<Gamma> x x"
  and weight_outside: "\<And>x. x \<notin> \<^bold>V \<Longrightarrow> weight \<Gamma> x = 0"
  and weight_finite [simp]: "\<And>x. weight \<Gamma> x \<noteq> \<top>"
begin

lemma web_weight_update:
  assumes "\<And>x. \<not> vertex \<Gamma> x \<Longrightarrow> w x = 0"
  and "\<And>x. w x \<noteq> \<top>"
  shows "web (\<Gamma>\<lparr>weight := w\<rparr>)"
by unfold_locales(simp_all add: A_in B_out A_vertex disjoint no_loop assms)

lemma currentI [intro?]:
  assumes "\<And>x. d_OUT f x \<le> weight \<Gamma> x"
  and "\<And>x. d_IN f x \<le> weight \<Gamma> x"
  and OUT_IN: "\<And>x. \<lbrakk> x \<notin> A \<Gamma>; x \<notin> B \<Gamma> \<rbrakk> \<Longrightarrow> d_OUT f x \<le> d_IN f x"
  and outside: "\<And>e. e \<notin> \<^bold>E \<Longrightarrow> f e = 0"
  shows "current \<Gamma> f"
proof
  show "d_IN f a = 0" if "a \<in> A \<Gamma>" for a using that
    by(auto simp add: d_IN_def nn_integral_0_iff emeasure_count_space_eq_0 A_in intro: outside)
  show "d_OUT f b = 0" if "b \<in> B \<Gamma>" for b using that
    by(auto simp add: d_OUT_def nn_integral_0_iff emeasure_count_space_eq_0 B_out intro: outside)
  then show "d_OUT f x \<le> d_IN f x" if "x \<notin> A \<Gamma>" for x using OUT_IN[OF that]
    by(cases "x \<in> B \<Gamma>") auto
qed(blast intro: assms)+

lemma currentD_finite_IN:
  assumes f: "current \<Gamma> f"
  shows "d_IN f x \<noteq> \<top>"
proof(cases "x \<in> \<^bold>V")
  case True
  have "d_IN f x \<le> weight \<Gamma> x" using f by(rule currentD_weight_IN)
  also have "\<dots> < \<top>" using True weight_finite[of x] by (simp add: less_top[symmetric])
  finally show ?thesis by simp
next
  case False
  then have "d_IN f x = 0"
    by(auto simp add: d_IN_def nn_integral_0_iff emeasure_count_space_eq_0 vertex_def intro: currentD_outside[OF f])
  thus ?thesis by simp
qed

lemma currentD_finite_OUT:
  assumes f: "current \<Gamma> f"
  shows "d_OUT f x \<noteq> \<top>"
proof(cases "x \<in> \<^bold>V")
  case True
  have "d_OUT f x \<le> weight \<Gamma> x" using f by(rule currentD_weight_OUT)
  also have "\<dots> < \<top>" using True weight_finite[of x] by (simp add: less_top[symmetric])
  finally show ?thesis by simp
next
  case False
  then have "d_OUT f x = 0"
    by(auto simp add: d_OUT_def nn_integral_0_iff emeasure_count_space_eq_0 vertex_def intro: currentD_outside[OF f])
  thus ?thesis by simp
qed

lemma currentD_finite:
  assumes f: "current \<Gamma> f"
  shows "f e \<noteq> \<top>"
proof(cases e)
  case (Pair x y)
  have "f (x, y) \<le> d_OUT f x" by (rule d_OUT_ge_point)
  also have "\<dots> < \<top>" using currentD_finite_OUT[OF f] by (simp add: less_top[symmetric])
  finally show ?thesis by(simp add: Pair)
qed

lemma web_quotient_web: "web (quotient_web \<Gamma> f)" (is "web ?\<Gamma>")
proof
  show "\<not> edge ?\<Gamma> y x" if "x \<in> A ?\<Gamma>" for x y using that by(auto intro: roofed_greaterI)
  show "\<not> edge ?\<Gamma> x y" if "x \<in> B ?\<Gamma>" for x y using that by(auto simp add: B_out)
  show "A ?\<Gamma> \<inter> B ?\<Gamma> = {}" using disjoint by auto
  show "A ?\<Gamma> \<subseteq> \<^bold>V\<^bsub>?\<Gamma>\<^esub>"
  proof
    fix x
    assume "x \<in> A ?\<Gamma>"
    hence \<E>: "x \<in> \<E> (TER f)" and x: "x \<notin> B \<Gamma>" using disjoint by auto
    from this(1) obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>" and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER f)"
      by(rule \<E>_E_RF) blast
    from p y x have "p \<noteq> []" by(auto simp add: rtrancl_path_simps)
    with rtrancl_path_nth[OF p, of 0] have "edge \<Gamma> x (p ! 0)" by simp
    moreover have "x \<notin> RF\<^sup>\<circ> (TER f)" using \<E> by(simp add: roofed_circ_def)
    moreover have "p ! 0 \<notin> RF (TER f)" using bypass \<open>p \<noteq> []\<close> by auto
    ultimately have "edge ?\<Gamma> x (p ! 0)" by simp
    thus "x \<in> \<^bold>V\<^bsub>?\<Gamma>\<^esub>" by(auto intro: vertexI1)
  qed
  show "\<not> edge ?\<Gamma> x x" for x by(simp add: no_loop)
  show "weight ?\<Gamma> x = 0" if "x \<notin> \<^bold>V\<^bsub>?\<Gamma>\<^esub>" for x
  proof(cases "x \<in> RF\<^sup>\<circ> (TER f) \<or> x \<in> TER f \<inter> B \<Gamma>")
    case True thus ?thesis by simp
  next
    case False
    hence RF: "x \<notin> RF\<^sup>\<circ> (TER f)" and B: "x \<in> B \<Gamma> \<Longrightarrow> x \<notin> TER f" by auto
    from RF obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>" and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER f)"
      apply(cases "x \<notin> RF (RF (TER f))")
       apply(auto elim!: not_roofedE)[1]
      apply(auto simp add: roofed_circ_def roofed_idem elim: essentialE_RF)
      done
    from that have "p = []" using p y B RF bypass
      by(auto 4 3 simp add: vertex_def dest!: rtrancl_path_nth[where i=0])
    with p have xy: "x = y" by(simp add: rtrancl_path_simps)
    with B y have "x \<notin> TER f" by simp
    hence RF': "x \<notin> RF (TER f)" using xy y by(subst RF_in_B) auto
    have "\<not> vertex \<Gamma> x"
    proof
      assume "vertex \<Gamma> x"
      then obtain x' where "edge \<Gamma> x' x" using xy y by(auto simp add: vertex_def B_out)
      moreover hence "x' \<notin> RF\<^sup>\<circ> (TER f)" using RF' by(auto dest: RF_circ_edge_forward)
      ultimately have "edge ?\<Gamma> x' x" using RF' by simp
      hence "vertex ?\<Gamma> x" by(rule vertexI2)
      with that show False by simp
    qed
    thus ?thesis by(simp add: weight_outside)
  qed
  show "weight ?\<Gamma> x \<noteq> \<top>" for x by simp
qed

end

locale countable_web = web \<Gamma>
  for \<Gamma> :: "('v, 'more) web_scheme" (structure)
  +
  assumes countable [simp]: "countable \<^bold>E"
begin

lemma countable_V [simp]: "countable \<^bold>V"
by(simp add: "\<^bold>V_def")

lemma countable_web_quotient_web: "countable_web (quotient_web \<Gamma> f)" (is "countable_web ?\<Gamma>")
proof -
  interpret r: web ?\<Gamma> by(rule web_quotient_web)
  show ?thesis
  proof
    have "\<^bold>E\<^bsub>?\<Gamma>\<^esub> \<subseteq> \<^bold>E" by auto
    then show "countable \<^bold>E\<^bsub>?\<Gamma>\<^esub>" by(rule countable_subset) simp
  qed
qed

end

subsection \<open>Subtraction of a wave\<close>

definition minus_web :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> ('v, 'more) web_scheme" (infixl "\<ominus>" 65) \<comment> \<open>Definition 6.6\<close>
where "\<Gamma> \<ominus> f = \<Gamma>\<lparr>weight := \<lambda>x. if x \<in> A \<Gamma> then weight \<Gamma> x - d_OUT f x else weight \<Gamma> x + d_OUT f x - d_IN f x\<rparr>"

lemma minus_web_sel [simp]:
  "edge (\<Gamma> \<ominus> f) = edge \<Gamma>"
  "weight (\<Gamma> \<ominus> f) x = (if x \<in> A \<Gamma> then weight \<Gamma> x - d_OUT f x else weight \<Gamma> x + d_OUT f x - d_IN f x)"
  "A (\<Gamma> \<ominus> f) = A \<Gamma>"
  "B (\<Gamma> \<ominus> f) = B \<Gamma>"
  "\<^bold>V\<^bsub>\<Gamma> \<ominus> f\<^esub> = \<^bold>V\<^bsub>\<Gamma>\<^esub>"
  "\<^bold>E\<^bsub>\<Gamma> \<ominus> f\<^esub> = \<^bold>E\<^bsub>\<Gamma>\<^esub>"
  "web.more (\<Gamma> \<ominus> f) = web.more \<Gamma>"
by(auto simp add: minus_web_def vertex_def)

lemma vertex_minus_web [simp]: "vertex (\<Gamma> \<ominus> f) = vertex \<Gamma>"
by(simp add: vertex_def fun_eq_iff)

lemma roofed_gen_minus_web [simp]: "roofed_gen (\<Gamma> \<ominus> f) = roofed_gen \<Gamma>"
by(simp add: fun_eq_iff roofed_def)

lemma minus_zero_current [simp]: "\<Gamma> \<ominus> zero_current = \<Gamma>"
by(rule web.equality)(simp_all add: fun_eq_iff)

lemma (in web) web_minus_web:
  assumes f: "current \<Gamma> f"
  shows "web (\<Gamma> \<ominus> f)"
unfolding minus_web_def
apply(rule web_weight_update)
apply(auto simp: weight_outside currentD_weight_IN[OF f] currentD_outside_OUT[OF f]
                 currentD_outside_IN[OF f] currentD_weight_OUT[OF f] currentD_finite_OUT[OF f])
done

subsection \<open>Bipartite webs\<close>

locale countable_bipartite_web =
  fixes \<Gamma> :: "('v, 'more) web_scheme" (structure)
  assumes bipartite_V: "\<^bold>V \<subseteq> A \<Gamma> \<union> B \<Gamma>"
  and A_vertex: "A \<Gamma> \<subseteq> \<^bold>V"
  and bipartite_E: "edge \<Gamma> x y \<Longrightarrow> x \<in> A \<Gamma> \<and> y \<in> B \<Gamma>"
  and disjoint: "A \<Gamma> \<inter> B \<Gamma> = {}"
  and weight_outside: "\<And>x. x \<notin> \<^bold>V \<Longrightarrow> weight \<Gamma> x = 0"
  and weight_finite [simp]: "\<And>x. weight \<Gamma> x \<noteq> \<top>"
  and countable_E [simp]: "countable \<^bold>E"
begin

lemma not_vertex: "\<lbrakk> x \<notin> A \<Gamma>; x \<notin> B \<Gamma> \<rbrakk> \<Longrightarrow> \<not> vertex \<Gamma> x"
using bipartite_V by blast

lemma no_loop: "\<not> edge \<Gamma> x x"
using disjoint by(auto dest: bipartite_E)

lemma edge_antiparallel: "edge \<Gamma> x y \<Longrightarrow> \<not> edge \<Gamma> y x"
using disjoint by(auto dest: bipartite_E)

lemma A_in: "x \<in> A \<Gamma> \<Longrightarrow> \<not> edge \<Gamma> y x"
using disjoint by(auto dest: bipartite_E)

lemma B_out: "x \<in> B \<Gamma> \<Longrightarrow> \<not> edge \<Gamma> x y"
using disjoint by(auto dest: bipartite_E)

sublocale countable_web using disjoint
by(unfold_locales)(auto simp add: A_in B_out A_vertex no_loop weight_outside)

lemma currentD_OUT':
  assumes f: "current \<Gamma> f"
  and x: "x \<notin> A \<Gamma>"
  shows "d_OUT f x = 0"
using currentD_outside_OUT[OF f, of x] x currentD_OUT[OF f, of x] bipartite_V by auto

lemma currentD_IN':
  assumes f: "current \<Gamma> f"
  and x: "x \<notin> B \<Gamma>"
  shows "d_IN f x = 0"
using currentD_outside_IN[OF f, of x] x currentD_IN[OF f, of x] bipartite_V by auto

lemma current_bipartiteI [intro?]:
  assumes OUT: "\<And>x. d_OUT f x \<le> weight \<Gamma> x"
  and IN: "\<And>x. d_IN f x \<le> weight \<Gamma> x"
  and outside: "\<And>e. e \<notin> \<^bold>E \<Longrightarrow> f e = 0"
  shows "current \<Gamma> f"
proof
  fix x
  assume "x \<notin> A \<Gamma>" "x \<notin> B \<Gamma>"
  hence "d_OUT f x = 0" by(auto simp add: d_OUT_def nn_integral_0_iff emeasure_count_space_eq_0 intro!: outside dest: bipartite_E)
  then show "d_OUT f x \<le> d_IN f x" by simp
qed(rule OUT IN outside)+

lemma wave_bipartiteI [intro?]:
  assumes sep: "separating \<Gamma> (TER f)"
  and f: "current \<Gamma> f"
  shows "wave \<Gamma> f"
using sep
proof(rule wave.intros)
  fix x
  assume "x \<notin> RF (TER f)"
  then consider "x \<notin> \<^bold>V" | "x \<in> \<^bold>V" "x \<in> B \<Gamma>" using separating_RF_A[OF sep] bipartite_V by auto
  then show "d_OUT f x = 0" using currentD_OUT[OF f, of x] currentD_outside_OUT[OF f, of x]
    by cases auto
qed


lemma web_flow_iff: "web_flow \<Gamma> f \<longleftrightarrow> current \<Gamma> f"
using bipartite_V by(auto simp add: web_flow.simps)

end

end
