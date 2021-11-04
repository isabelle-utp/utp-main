section\<open>Library of basic $\ZF$ results\label{sec:zf-lib}\<close>

theory ZF_Library
  imports
    "ZF-Constructible.Normal"

begin

text\<open>This theory gathers basic ``combinatorial'' results that can be proved
in $\ZF$ (that is, without using the Axiom of Choice $\AC$).
\<close>

text\<open>We begin by setting up math-friendly notation.\<close>

no_notation oadd (infixl \<open>++\<close> 65)
no_notation sum (infixr \<open>+\<close> 65)
notation oadd (infixl \<open>+\<close> 65)
notation nat (\<open>\<omega>\<close>)
notation csucc (\<open>_\<^sup>+\<close> [90])
no_notation Aleph (\<open>\<aleph>_\<close> [90] 90)
notation Aleph (\<open>\<aleph>\<^bsub>_\<^esub>\<close>)
syntax "_ge"  :: "[i,i] \<Rightarrow> o"  (infixl \<open>\<ge>\<close> 50)
translations "x \<ge> y" \<rightharpoonup> "y \<le> x"


subsection\<open>Some minimal arithmetic/ordinal stuff\<close>

lemma Un_leD1 : "i \<union> j \<le> k \<Longrightarrow> Ord(i) \<Longrightarrow> Ord(j) \<Longrightarrow> Ord(k) \<Longrightarrow> i \<le> k"
  by (rule Un_least_lt_iff[THEN iffD1[THEN conjunct1]],simp_all)

lemma Un_leD2 : "i \<union> j \<le> k \<Longrightarrow> Ord(i) \<Longrightarrow> Ord(j) \<Longrightarrow> Ord(k) \<Longrightarrow> j \<le> k"
  by (rule Un_least_lt_iff[THEN iffD1[THEN conjunct2]],simp_all)

lemma Un_memD1: "i \<union> j \<in> k \<Longrightarrow> Ord(i) \<Longrightarrow> Ord(j) \<Longrightarrow> Ord(k) \<Longrightarrow> i \<le> k"
  by (drule ltI, assumption, drule leI, rule Un_least_lt_iff[THEN iffD1[THEN conjunct1]],simp_all)

lemma Un_memD2 : "i \<union> j \<in> k \<Longrightarrow> Ord(i) \<Longrightarrow> Ord(j) \<Longrightarrow> Ord(k) \<Longrightarrow> j \<le> k"
  by (drule ltI, assumption, drule leI, rule Un_least_lt_iff[THEN iffD1[THEN conjunct2]],simp_all)

text\<open>This lemma allows to apply arithmetic simprocs to ordinal addition\<close>
lemma nat_oadd_add[simp]:
  assumes "m \<in> \<omega>" "n \<in> \<omega>" shows "n + m = n #+ m"
  using assms
  by induct simp_all

lemma Ord_has_max_imp_succ:
  assumes "Ord(\<gamma>)" "\<beta> \<in> \<gamma>" "\<forall>\<alpha>\<in>\<gamma>. \<alpha> \<le> \<beta>"
  shows "\<gamma> = succ(\<beta>)"
  using assms Ord_trans[of _ \<beta> \<gamma>]
  unfolding lt_def
  by (intro equalityI subsetI) auto

lemma Least_antitone:
  assumes
    "Ord(j)" "P(j)" "\<And>i. P(i) \<Longrightarrow> Q(i)"
  shows
    "(\<mu> i. Q(i)) \<le> (\<mu> i. P(i))"
  using assms LeastI2[of P j Q] Least_le by simp

lemma Least_set_antitone:
  "Ord(j) \<Longrightarrow> j\<in>A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<mu> i. i\<in>B) \<le> (\<mu> i. i\<in>A)"
  using subset_iff by (auto intro:Least_antitone)

lemma le_neq_imp_lt:
  "x\<le>y \<Longrightarrow> x\<noteq>y \<Longrightarrow> x<y"
  using ltD ltI[of x y] le_Ord2
  unfolding succ_def by auto

text\<open>Strict upper bound of a set of ordinals.\<close>
definition
  str_bound :: "i\<Rightarrow>i" where
  "str_bound(A) \<equiv> \<Union>a\<in>A. succ(a)"

lemma str_bound_type [TC]: "\<forall>a\<in>A. Ord(a) \<Longrightarrow> Ord(str_bound(A))"
  unfolding str_bound_def by auto

lemma str_bound_lt: "\<forall>a\<in>A. Ord(a) \<Longrightarrow> \<forall>a\<in>A. a < str_bound(A)"
  unfolding str_bound_def using str_bound_type
  by (blast intro:ltI)

lemma naturals_lt_nat[intro]: "n \<in> \<omega> \<Longrightarrow> n < \<omega>"
  unfolding lt_def by simp

text\<open>The next two lemmas are handy when one is constructing
some object recursively. The first handles injectivity (of recursively
constructed sequences of sets), while the second is helpful for
establishing a symmetry argument.\<close>
lemma Int_eq_zero_imp_not_eq:
  assumes
    "\<And>x y. x\<in>D \<Longrightarrow> y \<in> D \<Longrightarrow> x \<noteq> y \<Longrightarrow> A(x) \<inter> A(y) = 0"
    "\<And>x. x\<in>D \<Longrightarrow> A(x) \<noteq> 0" "a\<in>D" "b\<in>D" "a\<noteq>b"
  shows
    "A(a) \<noteq> A(b)"
  using assms by fastforce

lemma lt_neq_symmetry:
  assumes
    "\<And>\<alpha> \<beta>. \<alpha> \<in> \<gamma> \<Longrightarrow> \<beta> \<in> \<gamma> \<Longrightarrow> \<alpha> < \<beta> \<Longrightarrow> Q(\<alpha>,\<beta>)"
    "\<And>\<alpha> \<beta>. Q(\<alpha>,\<beta>) \<Longrightarrow> Q(\<beta>,\<alpha>)"
    "\<alpha> \<in> \<gamma>" "\<beta> \<in> \<gamma>" "\<alpha> \<noteq> \<beta>"
    "Ord(\<gamma>)"
  shows
    "Q(\<alpha>,\<beta>)"
proof -
  from assms
  consider "\<alpha><\<beta>" | "\<beta><\<alpha>"
    using Ord_linear_lt[of \<alpha> \<beta> thesis] Ord_in_Ord[of \<gamma>]
    by auto
  then
  show ?thesis by cases (auto simp add:assms)
qed

lemma cardinal_succ_not_0: "|A| = succ(n) \<Longrightarrow> A \<noteq> 0"
  by auto

lemma Ord_eq_Collect_lt: "i<\<alpha> \<Longrightarrow> {j\<in>\<alpha>. j<i} = i"
  \<comment> \<open>almost the same proof as @{thm nat_eq_Collect_lt}\<close>
  apply (rule equalityI)
  apply (blast dest: ltD)
  apply (auto simp add: Ord_mem_iff_lt)
  apply (rule Ord_trans ltI[OF _ lt_Ord]; auto simp add:lt_def dest:ltD)+
  done


subsection\<open>Manipulation of function spaces\<close>

definition
  Finite_to_one :: "[i,i] \<Rightarrow> i" where
  "Finite_to_one(X,Y) \<equiv> {f:X\<rightarrow>Y. \<forall>y\<in>Y. Finite({x\<in>X . f`x = y})}"

lemma Finite_to_oneI[intro]:
  assumes "f:X\<rightarrow>Y" "\<And>y. y\<in>Y \<Longrightarrow> Finite({x\<in>X . f`x = y})"
  shows "f \<in> Finite_to_one(X,Y)"
  using assms unfolding Finite_to_one_def by simp

lemma Finite_to_oneD[dest]:
  "f \<in> Finite_to_one(X,Y) \<Longrightarrow> f:X\<rightarrow>Y"
  "f \<in> Finite_to_one(X,Y) \<Longrightarrow> y\<in>Y \<Longrightarrow>  Finite({x\<in>X . f`x = y})"
  unfolding Finite_to_one_def by simp_all

lemma subset_Diff_Un: "X \<subseteq> A \<Longrightarrow> A = (A - X) \<union> X " by auto

lemma Diff_bij:
  assumes "\<forall>A\<in>F. X \<subseteq> A" shows "(\<lambda>A\<in>F. A-X) \<in> bij(F, {A-X. A\<in>F})"
  using assms unfolding bij_def inj_def surj_def
  by (auto intro:lam_type, subst subset_Diff_Un[of X]) auto

lemma function_space_nonempty:
  assumes "b\<in>B"
  shows "(\<lambda>x\<in>A. b) : A \<rightarrow> B"
  using assms lam_type by force

lemma vimage_lam: "(\<lambda>x\<in>A. f(x)) -`` B = { x\<in>A . f(x) \<in> B }"
  using lam_funtype[of A f, THEN [2] domain_type]
    lam_funtype[of A f, THEN [2] apply_equality] lamI[of _ A f]
  by auto blast

lemma range_fun_subset_codomain:
  assumes "h:B \<rightarrow> C"
  shows "range(h) \<subseteq> C"
  unfolding range_def domain_def converse_def using range_type[OF _ assms]  by auto

lemma Pi_rangeD:
  assumes "f\<in>Pi(A,B)" "b \<in> range(f)"
  shows "\<exists>a\<in>A. f`a = b"
  using assms apply_equality[OF _ assms(1), of _ b]
    domain_type[OF _ assms(1)] by auto

lemma Pi_range_eq: "f \<in> Pi(A,B) \<Longrightarrow> range(f) = {f ` x . x \<in> A}"
  using Pi_rangeD[of f A B] apply_rangeI[of f A B]
  by blast

lemma Pi_vimage_subset : "f \<in> Pi(A,B) \<Longrightarrow> f-``C \<subseteq> A"
  unfolding Pi_def by auto

lemma apply_in_range:
  assumes
    "Ord(\<gamma>)" "\<gamma>\<noteq>0" "f: A \<rightarrow> \<gamma>"
  shows
    "f`x\<in>\<gamma>"
proof (cases "x\<in>A")
  case True
  from assms \<open>x\<in>A\<close>
  show ?thesis
    using   domain_of_fun apply_rangeI  by simp
next
  case False
  from assms \<open>x\<notin>A\<close>
  show ?thesis
    using apply_0 Ord_0_lt ltD domain_of_fun by auto
qed

lemma range_eq_image:
  assumes "f:A\<rightarrow>B"
  shows "range(f) = f``A"
proof
  show "f `` A \<subseteq> range(f)"
    unfolding image_def by blast
  {
    fix x
    assume "x\<in>range(f)"
    with assms
    have "x\<in>f``A"
      using domain_of_fun[of f A "\<lambda>_. B"] by auto
  }
  then
  show "range(f) \<subseteq> f `` A" ..
qed

lemma Image_sub_codomain: "f:A\<rightarrow>B \<Longrightarrow> f``C \<subseteq> B"
  using image_subset fun_is_rel[of _ _ "\<lambda>_ . B"] by force

lemma inj_to_Image:
  assumes
    "f:A\<rightarrow>B" "f \<in> inj(A,B)"
  shows
    "f \<in> inj(A,f``A)"
  using assms inj_inj_range range_eq_image by force

lemma inj_imp_surj:
  fixes f b
  notes inj_is_fun[dest]
  defines [simp]: "ifx(x) \<equiv> if x\<in>range(f) then converse(f)`x else b"
  assumes "f \<in> inj(B,A)" "b\<in>B"
  shows "(\<lambda>x\<in>A. ifx(x)) \<in> surj(A,B)"
proof -
  from assms
  have "converse(f) \<in> surj(range(f),B)" "range(f) \<subseteq> A"
    "converse(f) : range(f) \<rightarrow> B"
    using inj_converse_surj range_fun_subset_codomain surj_is_fun by blast+
  with \<open>b\<in>B\<close>
  show "(\<lambda>x\<in>A. ifx(x)) \<in> surj(A,B)"
    unfolding surj_def
  proof (intro CollectI lam_type ballI; elim CollectE)
    fix y
    assume "y \<in> B" "\<forall>y\<in>B. \<exists>x\<in>range(f). converse(f) ` x = y"
    with \<open>range(f) \<subseteq> A\<close>
    show "\<exists>x\<in>A. (\<lambda>x\<in>A. ifx(x)) ` x = y"
      by (drule_tac bspec, auto)
  qed simp
qed

lemma fun_Pi_disjoint_Un:
  assumes "f \<in> Pi(A,B)" "g \<in> Pi(C,D)"  "A \<inter> C = 0"
  shows "f \<union> g \<in> Pi(A \<union> C, \<lambda>x. B(x) \<union> D(x))"
  using assms
  by (simp add: Pi_iff extension Un_rls) (unfold function_def, blast)

lemma Un_restrict_decomposition:
  assumes "f \<in> Pi(A,B)"
  shows "f = restrict(f, A \<inter> C) \<union> restrict(f, A - C)"
  using assms
proof (rule fun_extension)
  from assms
  have "restrict(f,A\<inter>C) \<union> restrict(f,A-C) \<in> Pi(A\<inter>C \<union> (A-C), \<lambda>x. B(x)\<union>B(x))"
    using restrict_type2[of f A B]
    by (rule_tac fun_Pi_disjoint_Un) force+
  moreover
  have "(A \<inter> C) \<union> (A - C) = A" by auto
  ultimately
  show "restrict(f, A \<inter> C) \<union> restrict(f, A - C) \<in> Pi(A, B)" by simp
next
  fix x
  assume "x \<in> A"
  with assms
  show "f ` x = (restrict(f, A \<inter> C) \<union> restrict(f, A - C)) ` x"
    using restrict fun_disjoint_apply1[of _ "restrict(f,_)"]
      fun_disjoint_apply2[of _ "restrict(f,_)"]
      domain_restrict[of f] apply_0 domain_of_fun
    by (cases "x\<in>C") simp_all
qed

lemma restrict_eq_imp_Un_into_Pi:
  assumes "f \<in> Pi(A,B)" "g \<in> Pi(C,D)" "restrict(f, A \<inter> C) = restrict(g, A \<inter> C)"
  shows "f \<union> g \<in> Pi(A \<union> C, \<lambda>x. B(x) \<union> D(x))"
proof -
  note assms
  moreover from this
  have "x \<notin> g \<Longrightarrow> x \<notin> restrict(g, A \<inter> C)" for x
    using restrict_subset[of g "A \<inter> C"] by auto
  moreover from calculation
  have "x \<in> f \<Longrightarrow> x \<in> restrict(f, A - C) \<or> x \<in> restrict(g, A \<inter> C)" for x
    by (subst (asm) Un_restrict_decomposition[of f A B "C"]) auto
  ultimately
  have "f \<union> g = restrict(f, A - C) \<union> g"
    using restrict_subset[of g "A \<inter> C"]
    by (subst Un_restrict_decomposition[of f A B "C"]) auto
  moreover
  have "A - C \<union> C = A \<union> C" by auto
  moreover
  note assms
  ultimately
  show ?thesis
    using fun_Pi_disjoint_Un[OF
        restrict_type2[of f A B "A-C"], of g C D]
    by auto
qed

lemma restrict_eq_imp_Un_into_Pi':
  assumes "f \<in> Pi(A,B)" "g \<in> Pi(C,D)"
    "restrict(f, domain(f) \<inter> domain(g)) = restrict(g, domain(f) \<inter> domain(g))"
  shows "f \<union> g \<in> Pi(A \<union> C, \<lambda>x. B(x) \<union> D(x))"
  using  assms domain_of_fun restrict_eq_imp_Un_into_Pi by simp

lemma restrict_subset_Sigma: "f \<subseteq> Sigma(C,B) \<Longrightarrow> restrict(f,A) \<subseteq> Sigma(A\<inter>C, B)"
  by (auto simp add: restrict_def)


subsection\<open>Finite sets\<close>

lemma Replace_sing1:
  "\<lbrakk> (\<exists>a. P(d,a)) \<and> (\<forall>y y'. P(d,y) \<longrightarrow> P(d,y') \<longrightarrow> y=y') \<rbrakk> \<Longrightarrow> \<exists>a. {y . x \<in> {d}, P(x,y)} = {a}"
  by blast

\<comment> \<open>Not really necessary\<close>
lemma Replace_sing2:
  assumes "\<forall>a. \<not> P(d,a)"
  shows "{y . x \<in> {d}, P(x,y)} = 0"
  using assms by auto

lemma Replace_sing3:
  assumes "\<exists>c e. c \<noteq> e \<and> P(d,c) \<and> P(d,e)"
  shows "{y . x \<in> {d}, P(x,y)} = 0"
proof -
  {
    fix z
    {
      assume "\<forall>y. P(d, y) \<longrightarrow> y = z"
      with assms
      have "False" by auto
    }
    then
    have "z \<notin> {y . x \<in> {d}, P(x,y)}"
      using Replace_iff by auto
  }
  then
  show ?thesis
    by (intro equalityI subsetI) simp_all
qed

lemma Replace_Un: "{b . a \<in> A \<union> B, Q(a, b)} =
        {b . a \<in> A, Q(a, b)} \<union> {b . a \<in> B, Q(a, b)}"
  by (intro equalityI subsetI) (auto simp add:Replace_iff)

lemma Replace_subset_sing: "\<exists>z. {y . x \<in> {d}, P(x,y)} \<subseteq> {z}"
proof -
  consider
    (1) "(\<exists>a. P(d,a)) \<and> (\<forall>y y'. P(d,y) \<longrightarrow> P(d,y') \<longrightarrow> y=y')" |
    (2) "\<forall>a. \<not> P(d,a)" | (3) "\<exists>c e. c \<noteq> e \<and> P(d,c) \<and> P(d,e)" by auto
  then
  show "\<exists>z. {y . x \<in> {d}, P(x,y)} \<subseteq> {z}"
  proof (cases)
    case 1
    then show ?thesis using Replace_sing1[of P d] by auto
  next
    case 2
    then show ?thesis by auto
  next
    case 3
    then show ?thesis using Replace_sing3[of P d] by auto
  qed
qed

lemma Finite_Replace: "Finite(A) \<Longrightarrow> Finite(Replace(A,Q))"
proof (induct rule:Finite_induct)
  case 0
  then
  show ?case by simp
next
  case (cons x B)
  moreover
  have "{b . a \<in> cons(x, B), Q(a, b)} =
        {b . a \<in> B, Q(a, b)} \<union> {b . a \<in> {x}, Q(a, b)}"
    using Replace_Un unfolding cons_def by auto
  moreover
  obtain d where "{b . a \<in> {x}, Q(a, b)} \<subseteq> {d}"
    using Replace_subset_sing[of _ Q] by blast
  moreover from this
  have "Finite({b . a \<in> {x}, Q(a, b)})"
    using subset_Finite by simp
  ultimately
  show ?case using subset_Finite by simp
qed

lemma Finite_domain: "Finite(A) \<Longrightarrow> Finite(domain(A))"
  using Finite_Replace unfolding domain_def
  by auto

lemma Finite_converse: "Finite(A) \<Longrightarrow> Finite(converse(A))"
  using Finite_Replace unfolding converse_def
  by auto

lemma Finite_range: "Finite(A) \<Longrightarrow> Finite(range(A))"
  using Finite_domain Finite_converse unfolding range_def
  by blast

lemma Finite_Sigma: "Finite(A) \<Longrightarrow> \<forall>x. Finite(B(x)) \<Longrightarrow> Finite(Sigma(A,B))"
  unfolding Sigma_def using Finite_RepFun Finite_Union
  by simp

lemma Finite_Pi: "Finite(A) \<Longrightarrow> \<forall>x. Finite(B(x)) \<Longrightarrow> Finite(Pi(A,B))"
  using Finite_Sigma
    Finite_Pow subset_Finite[of "Pi(A,B)" "Pow(Sigma(A,B))"]
  unfolding Pi_def
  by auto


subsection\<open>Basic results on equipollence, cardinality and related concepts\<close>

lemma lepollD[dest]: "A \<lesssim> B \<Longrightarrow> \<exists>f. f \<in> inj(A, B)"
  unfolding lepoll_def .

lemma lepollI[intro]: "f \<in> inj(A, B) \<Longrightarrow> A \<lesssim> B"
  unfolding lepoll_def by blast

lemma eqpollD[dest]: "A \<approx> B \<Longrightarrow> \<exists>f. f \<in> bij(A, B)"
  unfolding eqpoll_def .

declare bij_imp_eqpoll[intro]

lemma range_of_subset_eqpoll:
  assumes "f \<in> inj(X,Y)" "S \<subseteq> X"
  shows "S \<approx> f `` S"
  using assms restrict_bij by blast

text\<open>I thank Miguel Pagano for this proof.\<close>
lemma function_space_eqpoll_cong:
  assumes
    "A \<approx> A'" "B \<approx> B'"
  shows
    "A \<rightarrow> B \<approx> A' \<rightarrow> B'"
proof -
  from assms(1)[THEN eqpoll_sym] assms(2)
  obtain f g where "f \<in> bij(A',A)" "g \<in> bij(B,B')"
    by blast
  then
  have "converse(g) : B' \<rightarrow> B" "converse(f): A \<rightarrow> A'"
    using bij_converse_bij bij_is_fun by auto
  show ?thesis
    unfolding eqpoll_def
  proof (intro exI fg_imp_bijective, rule_tac [1-2] lam_type)
    fix F
    assume "F: A \<rightarrow> B"
    with \<open>f \<in> bij(A',A)\<close> \<open>g \<in> bij(B,B')\<close>
    show "g O F O f : A' \<rightarrow> B'"
      using bij_is_fun comp_fun by blast
  next
    fix F
    assume "F: A' \<rightarrow> B'"
    with \<open>converse(g) : B' \<rightarrow> B\<close> \<open>converse(f): A \<rightarrow> A'\<close>
    show "converse(g) O F O converse(f) : A \<rightarrow> B"
      using comp_fun by blast
  next
    from \<open>f\<in>_\<close> \<open>g\<in>_\<close> \<open>converse(f)\<in>_\<close> \<open>converse(g)\<in>_\<close>
    have "(\<And>x. x \<in> A' \<rightarrow> B' \<Longrightarrow> converse(g) O x O converse(f) \<in> A \<rightarrow> B)"
      using bij_is_fun comp_fun by blast
    then
    have "(\<lambda>x\<in>A \<rightarrow> B. g O x O f) O (\<lambda>x\<in>A' \<rightarrow> B'. converse(g) O x O converse(f))
          =  (\<lambda>x\<in>A' \<rightarrow> B' . (g O converse(g)) O x O (converse(f) O f))"
      using lam_cong comp_assoc comp_lam[of "A' \<rightarrow> B'" ] by auto
    also
    have "... = (\<lambda>x\<in>A' \<rightarrow> B' . id(B') O x O (id(A')))"
      using left_comp_inverse[OF bij_is_inj[OF \<open>f\<in>_\<close>]]
        right_comp_inverse[OF bij_is_surj[OF \<open>g\<in>_\<close>]]
      by auto
    also
    have "... = (\<lambda>x\<in>A' \<rightarrow> B' . x)"
      using left_comp_id[OF fun_is_rel] right_comp_id[OF fun_is_rel]  lam_cong by auto
    also
    have "... = id(A'\<rightarrow>B')" unfolding id_def by simp
    finally
    show "(\<lambda>x\<in>A -> B. g O x O f) O (\<lambda>x\<in>A' -> B'. converse(g) O x O converse(f)) = id(A' -> B')" .
  next
    from \<open>f\<in>_\<close> \<open>g\<in>_\<close>
    have "(\<And>x. x \<in> A \<rightarrow> B \<Longrightarrow> g O x O f \<in> A' \<rightarrow> B')"
      using bij_is_fun comp_fun by blast
    then
    have "(\<lambda>x\<in>A' -> B'. converse(g) O x O converse(f)) O (\<lambda>x\<in>A -> B. g O x O f)
          = (\<lambda>x\<in>A \<rightarrow> B . (converse(g) O g) O x O (f O converse(f)))"
      using comp_lam comp_assoc by auto
    also
    have "... = (\<lambda>x\<in>A \<rightarrow> B . id(B) O x O (id(A)))"
      using
        right_comp_inverse[OF bij_is_surj[OF \<open>f\<in>_\<close>]]
        left_comp_inverse[OF bij_is_inj[OF \<open>g\<in>_\<close>]] lam_cong
      by auto
    also
    have "... = (\<lambda>x\<in>A \<rightarrow> B . x)"
      using left_comp_id[OF fun_is_rel] right_comp_id[OF fun_is_rel] lam_cong by auto
    also
    have "... = id(A\<rightarrow>B)" unfolding id_def by simp
    finally
    show "(\<lambda>x\<in>A' \<rightarrow> B'. converse(g) O x O converse(f)) O (\<lambda>x\<in>A -> B. g O x O f) = id(A -> B)" .
  qed
qed

lemma curry_eqpoll:
  fixes d \<nu>1 \<nu>2  \<kappa>
  shows "\<nu>1 \<rightarrow> \<nu>2 \<rightarrow> \<kappa> \<approx> \<nu>1 \<times> \<nu>2 \<rightarrow> \<kappa>"
  unfolding eqpoll_def
proof (intro exI, rule lam_bijective,
    rule_tac [1-2] lam_type, rule_tac [2] lam_type)
  fix f z
  assume "f : \<nu>1 \<rightarrow> \<nu>2 \<rightarrow> \<kappa>" "z \<in> \<nu>1 \<times> \<nu>2"
  then
  show "f`fst(z)`snd(z) \<in> \<kappa>"
    by simp
next
  fix f x y
  assume "f : \<nu>1 \<times> \<nu>2 \<rightarrow> \<kappa>" "x\<in>\<nu>1" "y\<in>\<nu>2"
  then
  show "f`\<langle>x,y\<rangle> \<in> \<kappa>" by simp
next \<comment> \<open>one composition is the identity:\<close>
  fix f
  assume "f : \<nu>1 \<times> \<nu>2 \<rightarrow> \<kappa>"
  then
  show "(\<lambda>x\<in>\<nu>1 \<times> \<nu>2. (\<lambda>x\<in>\<nu>1. \<lambda>xa\<in>\<nu>2. f ` \<langle>x, xa\<rangle>) ` fst(x) ` snd(x)) = f"
    by (auto intro:fun_extension)
qed simp \<comment> \<open>the other composition follows automatically\<close>

lemma Pow_eqpoll_function_space:
  fixes d X
  notes bool_of_o_def [simp]
  defines [simp]:"d(A) \<equiv> (\<lambda>x\<in>X. bool_of_o(x\<in>A))"
    \<comment> \<open>the witnessing map for the thesis:\<close>
  shows "Pow(X) \<approx> X \<rightarrow> 2"
  unfolding eqpoll_def
proof (intro exI, rule lam_bijective)
  \<comment> \<open>We give explicit mutual inverses\<close>
  fix A
  assume "A\<in>Pow(X)"
  then
  show "d(A) : X \<rightarrow> 2"
    using lam_type[of _ "\<lambda>x. bool_of_o(x\<in>A)" "\<lambda>_. 2"]
    by force
  from \<open>A\<in>Pow(X)\<close>
  show "{y\<in>X. d(A)`y = 1} = A"
    by (auto)
next
  fix f
  assume "f: X\<rightarrow>2"
  then
  show "d({y \<in> X . f ` y = 1}) = f"
    using apply_type[OF \<open>f: X\<rightarrow>2\<close>]
    by (force intro:fun_extension)
qed blast

lemma cantor_inj: "f \<notin> inj(Pow(A),A)"
  using inj_imp_surj[OF _ Pow_bottom] cantor_surj by blast

definition
  cexp :: "[i,i] \<Rightarrow> i" ("_\<^bsup>\<up>_\<^esup>" [76,1] 75) where
  "\<kappa>\<^bsup>\<up>\<nu>\<^esup> \<equiv> |\<nu> \<rightarrow> \<kappa>|"

lemma Card_cexp: "Card(\<kappa>\<^bsup>\<up>\<nu>\<^esup>)"
  unfolding cexp_def Card_cardinal by simp

lemma eq_csucc_ord:
  "Ord(i) \<Longrightarrow> i\<^sup>+ = |i|\<^sup>+"
  using Card_lt_iff Least_cong unfolding csucc_def by auto

text\<open>I thank Miguel Pagano for this proof.\<close>
lemma lesspoll_csucc:
  assumes "Ord(\<kappa>)"
  shows "d \<prec> \<kappa>\<^sup>+ \<longleftrightarrow> d \<lesssim> \<kappa>"
proof
  assume "d \<prec> \<kappa>\<^sup>+"
  moreover
  note Card_is_Ord \<open>Ord(\<kappa>)\<close>
  moreover from calculation
  have "\<kappa> < \<kappa>\<^sup>+" "Card(\<kappa>\<^sup>+)"
    using Ord_cardinal_eqpoll csucc_basic by simp_all
  moreover from calculation
  have "d \<prec> |\<kappa>|\<^sup>+" "Card(|\<kappa>|)" "d \<approx> |d|"
    using eq_csucc_ord[of \<kappa>] lesspoll_imp_eqpoll eqpoll_sym by simp_all
  moreover from calculation
  have "|d| < |\<kappa>|\<^sup>+"
    using lesspoll_cardinal_lt csucc_basic by simp
  moreover from calculation
  have "|d| \<lesssim> |\<kappa>|"
    using Card_lt_csucc_iff le_imp_lepoll by simp
  moreover from calculation
  have "|d| \<lesssim> \<kappa>"
    using lepoll_eq_trans Ord_cardinal_eqpoll by simp
  ultimately
  show "d \<lesssim> \<kappa>"
    using eq_lepoll_trans by simp
next
  from \<open>Ord(\<kappa>)\<close>
  have "\<kappa> < \<kappa>\<^sup>+" "Card(\<kappa>\<^sup>+)"
    using csucc_basic by simp_all
  moreover
  assume "d \<lesssim> \<kappa>"
  ultimately
  have "d \<lesssim> \<kappa>\<^sup>+"
    using le_imp_lepoll leI lepoll_trans by simp
  moreover
  from \<open>d \<lesssim> \<kappa>\<close> \<open>Ord(\<kappa>)\<close>
  have "\<kappa>\<^sup>+ \<lesssim> \<kappa>" if "d \<approx> \<kappa>\<^sup>+"
    using eqpoll_sym[OF that] eq_lepoll_trans[OF _ \<open>d\<lesssim>\<kappa>\<close>] by simp
  moreover from calculation \<open>Card(_)\<close>
  have "\<not> d \<approx> \<kappa>\<^sup>+"
    using lesspoll_irrefl lesspoll_trans1 lt_Card_imp_lesspoll[OF _ \<open>\<kappa> <_\<close>]
    by auto
  ultimately
  show "d \<prec> \<kappa>\<^sup>+"
    unfolding lesspoll_def by simp
qed

abbreviation
  Infinite :: "i\<Rightarrow>o" where
  "Infinite(X) \<equiv> \<not> Finite(X)"

lemma Infinite_not_empty: "Infinite(X) \<Longrightarrow> X \<noteq> 0"
  using empty_lepollI by auto

lemma Infinite_imp_nats_lepoll:
  assumes "Infinite(X)" "n \<in> \<omega>"
  shows "n \<lesssim> X"
  using \<open>n \<in> \<omega>\<close>
proof (induct)
  case 0
  then
  show ?case using empty_lepollI by simp
next
  case (succ x)
  show ?case
  proof -
    from \<open>Infinite(X)\<close> and \<open>x \<in> \<omega>\<close>
    have "\<not> (x \<approx> X)"
      using eqpoll_sym unfolding Finite_def by auto
    with \<open>x \<lesssim> X\<close>
    obtain f where "f \<in> inj(x,X)" "f \<notin> surj(x,X)"
      unfolding bij_def eqpoll_def by auto
    moreover from this
    obtain b where "b \<in> X" "\<forall>a\<in>x. f`a \<noteq> b"
      using inj_is_fun unfolding surj_def by auto
    ultimately
    have "f \<in> inj(x,X-{b})"
      unfolding inj_def by (auto intro:Pi_type)
    then
    have "cons(\<langle>x, b\<rangle>, f) \<in> inj(succ(x), cons(b, X - {b}))"
      using inj_extend[of f x "X-{b}" x b] unfolding succ_def
      by (auto dest:mem_irrefl)
    moreover from \<open>b\<in>X\<close>
    have "cons(b, X - {b}) = X" by auto
    ultimately
    show "succ(x) \<lesssim> X" by auto
  qed
qed

lemma zero_lesspoll: assumes "0<\<kappa>" shows "0 \<prec> \<kappa>"
  using assms eqpoll_0_iff[THEN iffD1, of \<kappa>] eqpoll_sym
  unfolding lesspoll_def lepoll_def
  by (auto simp add:inj_def)

lemma lepoll_nat_imp_Infinite: "\<omega> \<lesssim> X \<Longrightarrow> Infinite(X)"
proof (rule ccontr, simp)
  assume "\<omega> \<lesssim> X" "Finite(X)"
  moreover from this
  obtain n where "X \<approx> n" "n \<in> \<omega>"
    unfolding Finite_def by auto
  moreover from calculation
  have "\<omega> \<lesssim> n"
    using lepoll_eq_trans by simp
  ultimately
  show "False"
    using lepoll_nat_imp_Finite nat_not_Finite by simp
qed

lemma InfCard_imp_Infinite: "InfCard(\<kappa>) \<Longrightarrow> Infinite(\<kappa>)"
  using le_imp_lepoll[THEN lepoll_nat_imp_Infinite, of \<kappa>]
  unfolding InfCard_def by simp

lemma lt_surj_empty_imp_Card:
  assumes "Ord(\<kappa>)" "\<And>\<alpha>. \<alpha> < \<kappa> \<Longrightarrow> surj(\<alpha>,\<kappa>) = 0"
  shows "Card(\<kappa>)"
proof -
  {
    assume "|\<kappa>| < \<kappa>"
    with assms
    have "False"
      using LeastI[of "\<lambda>i. i \<approx> \<kappa>" \<kappa>, OF eqpoll_refl]
        Least_le[of "\<lambda>i. i \<approx> \<kappa>" "|\<kappa>|", OF Ord_cardinal_eqpoll]
      unfolding Card_def cardinal_def eqpoll_def bij_def
      by simp
  }
  with assms
  show ?thesis
    using Ord_cardinal_le[of \<kappa>] not_lt_imp_le[of "|\<kappa>|" \<kappa>] le_anti_sym
    unfolding Card_def by auto
qed


subsection\<open>Morphisms of binary relations\<close>

text\<open>The main case of interest is in the case of partial orders.\<close>

lemma mono_map_mono:
  assumes
    "f \<in> mono_map(A,r,B,s)" "B \<subseteq> C"
  shows
    "f \<in> mono_map(A,r,C,s)"
  unfolding mono_map_def
proof (intro CollectI ballI impI)
  from \<open>f \<in> mono_map(A,_,B,_)\<close>
  have "f: A \<rightarrow> B"
    using mono_map_is_fun by simp
  with \<open>B\<subseteq>C\<close>
  show "f: A \<rightarrow> C"
    using fun_weaken_type by simp
  fix x y
  assume "x\<in>A" "y\<in>A" "\<langle>x,y\<rangle> \<in> r"
  moreover from this and \<open>f: A \<rightarrow> B\<close>
  have "f`x \<in> B" "f`y \<in> B"
    using apply_type by simp_all
  moreover
  note \<open>f \<in> mono_map(_,r,_,s)\<close>
  ultimately
  show "\<langle>f ` x, f ` y\<rangle> \<in> s"
    unfolding mono_map_def by blast
qed

lemma ordertype_zero_imp_zero: "ordertype(A,r) = 0 \<Longrightarrow> A = 0"
  using ordermap_type[of A r]
  by (cases "A=0") auto

lemma mono_map_increasing:
  "j\<in>mono_map(A,r,B,s) \<Longrightarrow> a\<in>A \<Longrightarrow> c\<in>A \<Longrightarrow> \<langle>a,c\<rangle>\<in>r \<Longrightarrow> \<langle>j`a,j`c\<rangle>\<in>s"
  unfolding mono_map_def by simp

lemma linear_mono_map_reflects:
  assumes
    "linear(\<alpha>,r)" "trans[\<beta>](s)" "irrefl(\<beta>,s)" "f\<in>mono_map(\<alpha>,r,\<beta>,s)"
    "x\<in>\<alpha>" "y\<in>\<alpha>" "\<langle>f`x,f`y\<rangle>\<in>s"
  shows
    "\<langle>x,y\<rangle>\<in>r"
proof -
  from \<open>f\<in>mono_map(_,_,_,_)\<close>
  have preserves:"x\<in>\<alpha> \<Longrightarrow> y\<in>\<alpha> \<Longrightarrow> \<langle>x,y\<rangle>\<in>r \<Longrightarrow> \<langle>f`x,f`y\<rangle>\<in>s" for x y
    unfolding mono_map_def by blast
  {
    assume "\<langle>x, y\<rangle> \<notin> r" "x\<in>\<alpha>" "y\<in>\<alpha>"
    moreover
    note \<open>\<langle>f`x,f`y\<rangle>\<in>s\<close> and \<open>linear(\<alpha>,r)\<close>
    moreover from calculation
    have "y = x \<or> \<langle>y,x\<rangle>\<in>r"
      unfolding linear_def by blast
    moreover
    note preserves [of y x]
    ultimately
    have "y = x \<or> \<langle>f`y, f`x\<rangle>\<in> s" by blast
    moreover from \<open>f\<in>mono_map(_,_,\<beta>,_)\<close> \<open>x\<in>\<alpha>\<close> \<open>y\<in>\<alpha>\<close>
    have "f`x\<in>\<beta>" "f`y\<in>\<beta>"
      using apply_type[OF mono_map_is_fun] by simp_all
    moreover
    note \<open>\<langle>f`x,f`y\<rangle>\<in>s\<close>  \<open>trans[\<beta>](s)\<close> \<open>irrefl(\<beta>,s)\<close>
    ultimately
    have "False"
      using trans_onD[of \<beta> s "f`x" "f`y" "f`x"] irreflE by blast
  }
  with assms
  show "\<langle>x,y\<rangle>\<in>r" by blast
qed

lemma irrefl_Memrel: "irrefl(x, Memrel(x))"
  unfolding irrefl_def using mem_irrefl by auto

lemmas Memrel_mono_map_reflects = linear_mono_map_reflects
  [OF well_ord_is_linear[OF well_ord_Memrel] well_ord_is_trans_on[OF well_ord_Memrel]
    irrefl_Memrel]

\<comment> \<open>Same proof as Paulson's @{thm mono_map_is_inj}\<close>
lemma mono_map_is_inj':
  "\<lbrakk> linear(A,r);  irrefl(B,s);  f \<in> mono_map(A,r,B,s) \<rbrakk> \<Longrightarrow> f \<in> inj(A,B)"
  unfolding irrefl_def mono_map_def inj_def using linearE
  by (clarify, rename_tac x w)
    (erule_tac x=w and y=x in linearE, assumption+, (force intro: apply_type)+)

lemma mono_map_imp_ord_iso_image:
  assumes
    "linear(\<alpha>,r)" "trans[\<beta>](s)"  "irrefl(\<beta>,s)" "f\<in>mono_map(\<alpha>,r,\<beta>,s)"
  shows
    "f \<in> ord_iso(\<alpha>,r,f``\<alpha>,s)"
  unfolding ord_iso_def
proof (intro CollectI ballI iffI)
  \<comment> \<open>Enough to show it's bijective and preserves both ways\<close>
  from assms
  have "f \<in> inj(\<alpha>,\<beta>)"
    using mono_map_is_inj' by blast
  moreover from \<open>f \<in> mono_map(_,_,_,_)\<close>
  have "f \<in> surj(\<alpha>, f``\<alpha>)"
    unfolding mono_map_def using surj_image by auto
  ultimately
  show "f \<in> bij(\<alpha>, f``\<alpha>)"
    unfolding bij_def using inj_is_fun inj_to_Image by simp
  from \<open>f\<in>mono_map(_,_,_,_)\<close>
  show "x\<in>\<alpha> \<Longrightarrow> y\<in>\<alpha> \<Longrightarrow> \<langle>x,y\<rangle>\<in>r \<Longrightarrow> \<langle>f`x,f`y\<rangle>\<in>s" for x y
    unfolding mono_map_def by blast
  with assms
  show "\<langle>f`x,f`y\<rangle>\<in>s \<Longrightarrow> x\<in>\<alpha> \<Longrightarrow> y\<in>\<alpha> \<Longrightarrow> \<langle>x,y\<rangle>\<in>r" for x y
    using linear_mono_map_reflects
    by blast
qed

text\<open>We introduce the following notation for strictly increasing maps
between ordinals.\<close>

abbreviation
  mono_map_Memrel :: "[i,i] \<Rightarrow> i" (infixr \<open>\<rightarrow>\<^sub><\<close> 60) where
  "\<alpha> \<rightarrow>\<^sub>< \<beta> \<equiv> mono_map(\<alpha>,Memrel(\<alpha>),\<beta>,Memrel(\<beta>))"

lemma mono_map_imp_ord_iso_Memrel:
  assumes
    "Ord(\<alpha>)" "Ord(\<beta>)" "f:\<alpha> \<rightarrow>\<^sub>< \<beta>"
  shows
    "f \<in> ord_iso(\<alpha>,Memrel(\<alpha>),f``\<alpha>,Memrel(\<beta>))"
  using assms mono_map_imp_ord_iso_image[OF well_ord_is_linear[OF well_ord_Memrel]
      well_ord_is_trans_on[OF well_ord_Memrel] irrefl_Memrel] by blast

lemma mono_map_ordertype_image':
  assumes
    "X\<subseteq>\<alpha>" "Ord(\<alpha>)" "Ord(\<beta>)" "f \<in> mono_map(X,Memrel(\<alpha>),\<beta>,Memrel(\<beta>))"
  shows
    "ordertype(f``X,Memrel(\<beta>)) = ordertype(X,Memrel(\<alpha>))"
  using assms mono_map_is_fun[of f X _ \<beta>]  ordertype_eq
    mono_map_imp_ord_iso_image[OF well_ord_is_linear[OF well_ord_Memrel, THEN linear_subset]
      well_ord_is_trans_on[OF well_ord_Memrel] irrefl_Memrel, of \<alpha> X \<beta> f]
    well_ord_subset[OF well_ord_Memrel]  Image_sub_codomain[of f X \<beta> X] by auto

lemma mono_map_ordertype_image:
  assumes
    "Ord(\<alpha>)" "Ord(\<beta>)" "f:\<alpha> \<rightarrow>\<^sub>< \<beta>"
  shows
    "ordertype(f``\<alpha>,Memrel(\<beta>)) = \<alpha>"
  using assms mono_map_is_fun ordertype_Memrel ordertype_eq[of f \<alpha> "Memrel(\<alpha>)"]
    mono_map_imp_ord_iso_Memrel well_ord_subset[OF well_ord_Memrel] Image_sub_codomain[of _ \<alpha>]
  by auto

lemma apply_in_image: "f:A\<rightarrow>B \<Longrightarrow> a\<in>A \<Longrightarrow> f`a \<in> f``A"
  using range_eq_image apply_rangeI[of f]  by simp

lemma Image_subset_Ord_imp_lt:
  assumes
    "Ord(\<alpha>)" "h``A \<subseteq> \<alpha>" "x\<in>domain(h)" "x\<in>A" "function(h)"
  shows
    "h`x < \<alpha>"
  using assms
  unfolding domain_def using imageI ltI function_apply_equality by auto

lemma ordermap_le_arg:
  assumes
    "X\<subseteq>\<beta>" "x\<in>X" "Ord(\<beta>)"
  shows
    "x\<in>X \<Longrightarrow> ordermap(X,Memrel(\<beta>))`x\<le>x"
proof (induct rule:Ord_induct[OF subsetD, OF assms])
  case (1 x)
  have "wf[X](Memrel(\<beta>))"
    using wf_imp_wf_on[OF wf_Memrel] .
  with 1
  have "ordermap(X,Memrel(\<beta>))`x = {ordermap(X,Memrel(\<beta>))`y . y\<in>{y\<in>X . y\<in>x \<and> y\<in>\<beta>}}"
    using ordermap_unfold Ord_trans[of _ x \<beta>] by auto
  also from assms
  have "... = {ordermap(X,Memrel(\<beta>))`y . y\<in>{y\<in>X . y\<in>x}}"
    using Ord_trans[of _ x \<beta>] Ord_in_Ord by blast
  finally
  have ordm:"ordermap(X,Memrel(\<beta>))`x = {ordermap(X,Memrel(\<beta>))`y . y\<in>{y\<in>X . y\<in>x}}" .
  from 1
  have "y\<in>x \<Longrightarrow> y\<in>X \<Longrightarrow> ordermap(X,Memrel(\<beta>))`y \<le> y" for y by simp
  with \<open>x\<in>\<beta>\<close> and \<open>Ord(\<beta>)\<close>
  have "y\<in>x \<Longrightarrow> y\<in>X \<Longrightarrow> ordermap(X,Memrel(\<beta>))`y \<in> x" for y
    using ltI[OF _ Ord_in_Ord[of \<beta> x]] lt_trans1 ltD by blast
  with ordm
  have "ordermap(X,Memrel(\<beta>))`x \<subseteq> x" by auto
  with \<open>x\<in>X\<close> assms
  show ?case
    using subset_imp_le Ord_in_Ord[of \<beta> x] Ord_ordermap
      well_ord_subset[OF well_ord_Memrel, of \<beta>] by force
qed

lemma subset_imp_ordertype_le:
  assumes
    "X\<subseteq>\<beta>" "Ord(\<beta>)"
  shows
    "ordertype(X,Memrel(\<beta>))\<le>\<beta>"
proof -
  {
    fix x
    assume "x\<in>X"
    with assms
    have "ordermap(X,Memrel(\<beta>))`x \<le> x"
      using ordermap_le_arg by simp
    with \<open>x\<in>X\<close> and assms
    have "ordermap(X,Memrel(\<beta>))`x \<in> \<beta>" (is "?y \<in> _")
      using ltD[of ?y "succ(x)"] Ord_trans[of  ?y x \<beta>] by auto
  }
  then
  have "ordertype(X, Memrel(\<beta>)) \<subseteq> \<beta>"
    using ordertype_unfold[of X] by auto
  with assms
  show ?thesis
    using subset_imp_le Ord_ordertype[OF well_ord_subset, OF well_ord_Memrel] by simp
qed

lemma mono_map_imp_le:
  assumes
    "f\<in>mono_map(\<alpha>, Memrel(\<alpha>),\<beta>, Memrel(\<beta>))" "Ord(\<alpha>)" "Ord(\<beta>)"
  shows
    "\<alpha>\<le>\<beta>"
proof -
  from assms
  have "f \<in> \<langle>\<alpha>, Memrel(\<alpha>)\<rangle> \<cong> \<langle>f``\<alpha>, Memrel(\<beta>)\<rangle>"
    using mono_map_imp_ord_iso_Memrel by simp
  then
  have "converse(f) \<in> \<langle>f``\<alpha>, Memrel(\<beta>)\<rangle> \<cong> \<langle>\<alpha>, Memrel(\<alpha>)\<rangle>"
    using ord_iso_sym by simp
  with \<open>Ord(\<alpha>)\<close>
  have "\<alpha> = ordertype(f``\<alpha>,Memrel(\<beta>))"
    using ordertype_eq well_ord_Memrel ordertype_Memrel by auto
  also from assms
  have "ordertype(f``\<alpha>,Memrel(\<beta>)) \<le> \<beta>"
    using subset_imp_ordertype_le mono_map_is_fun[of f] Image_sub_codomain[of f] by force
  finally
  show ?thesis .
qed

\<comment> \<open>\<^term>\<open>Ord(A) \<Longrightarrow> f \<in> mono_map(A, Memrel(A), B, Memrel(Aa)) \<Longrightarrow> f \<in> inj(A, B)\<close>\<close> 
lemmas Memrel_mono_map_is_inj = mono_map_is_inj
  [OF well_ord_is_linear[OF well_ord_Memrel]
    wf_imp_wf_on[OF wf_Memrel]]

lemma mono_mapI:
  assumes "f: A\<rightarrow>B" "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> \<langle>x,y\<rangle>\<in>r \<Longrightarrow> \<langle>f`x,f`y\<rangle>\<in>s"
  shows   "f \<in> mono_map(A,r,B,s)"
  unfolding mono_map_def using assms by simp

lemmas mono_mapD = mono_map_is_fun mono_map_increasing

bundle mono_map_rules =  mono_mapI[intro!] mono_map_is_fun[dest] mono_mapD[dest]

lemma nats_le_InfCard:
  assumes "n \<in> \<omega>" "InfCard(\<kappa>)"
  shows "n \<le> \<kappa>"
  using assms Ord_is_Transset
    le_trans[of n \<omega> \<kappa>, OF le_subset_iff[THEN iffD2]]
  unfolding InfCard_def Transset_def by simp

lemma nat_into_InfCard:
  assumes "n \<in> \<omega>" "InfCard(\<kappa>)"
  shows "n \<in> \<kappa>"
  using assms  le_imp_subset[of \<omega> \<kappa>]
  unfolding InfCard_def by auto


subsection\<open>Alephs are infinite cardinals\<close>

lemma Aleph_zero_eq_nat: "\<aleph>\<^bsub>0\<^esub> = \<omega>"
  unfolding Aleph_def by simp

lemma InfCard_Aleph:
  notes Aleph_zero_eq_nat[simp]
  assumes "Ord(\<alpha>)"
  shows "InfCard(\<aleph>\<^bsub>\<alpha>\<^esub>)"
proof -
  have "\<not> (\<aleph>\<^bsub>\<alpha>\<^esub> \<in> \<omega>)"
  proof (cases "\<alpha>=0")
    case True
    then show ?thesis using mem_irrefl by auto
  next
    case False
    with \<open>Ord(\<alpha>)\<close>
    have "\<omega> \<in> \<aleph>\<^bsub>\<alpha>\<^esub>" using Ord_0_lt[of \<alpha>] ltD  by (auto dest:Aleph_increasing)
    then show ?thesis using foundation by blast
  qed
  with \<open>Ord(\<alpha>)\<close>
  have "\<not> (|\<aleph>\<^bsub>\<alpha>\<^esub>| \<in> \<omega>)"
    using Card_cardinal_eq by auto
  then
  have "\<not> Finite(\<aleph>\<^bsub>\<alpha>\<^esub>)" by auto
  with \<open>Ord(\<alpha>)\<close>
  show ?thesis
    using Inf_Card_is_InfCard by simp
qed

lemmas Limit_Aleph = InfCard_Aleph[THEN InfCard_is_Limit]

lemmas Aleph_cont = Normal_imp_cont[OF Normal_Aleph]
lemmas Aleph_sup = Normal_Union[OF _ _ Normal_Aleph]

bundle Ord_dests = Limit_is_Ord[dest] Card_is_Ord[dest]
bundle Aleph_dests = Aleph_cont[dest] Aleph_sup[dest]
bundle Aleph_intros = Aleph_increasing[intro!]
bundle Aleph_mem_dests = Aleph_increasing[OF ltI, THEN ltD, dest]


end