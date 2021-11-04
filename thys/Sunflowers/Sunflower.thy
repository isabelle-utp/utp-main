(* author: R. Thiemann *)

section \<open>Sunflowers\<close>

text \<open>Sunflowers are sets of sets, such that whenever an element
  is contained in at least two of the sets, 
  then it is contained in all of the sets.\<close>

theory Sunflower
  imports Main
    "HOL-Library.FuncSet"
begin

definition sunflower :: "'a set set \<Rightarrow> bool" where
  "sunflower S = (\<forall> x. (\<exists> A B. A \<in> S \<and> B \<in> S \<and> A \<noteq> B \<and> 
     x \<in> A \<and> x \<in> B)
    \<longrightarrow> (\<forall> A. A \<in> S \<longrightarrow> x \<in> A))" 

lemma sunflower_subset: "F \<subseteq> G \<Longrightarrow> sunflower G \<Longrightarrow> sunflower F" 
  unfolding sunflower_def by blast

lemma pairwise_disjnt_imp_sunflower: 
  "pairwise disjnt F \<Longrightarrow> sunflower F" 
  unfolding sunflower_def 
  by (metis disjnt_insert1 mk_disjoint_insert pairwiseD)

lemma card2_sunflower: assumes "finite S" and "card S \<le> 2" 
  shows "sunflower S" 
proof -
  from assms have "card S = 0 \<or> card S = Suc 0 \<or> card S = 2" by linarith
  with \<open>finite S\<close> obtain A B where "S = {} \<or> S = {A} \<or> S = {A,B}" 
    using card_2_iff[of S] card_1_singleton_iff[of S] by auto
  thus ?thesis unfolding sunflower_def by auto
qed

lemma empty_sunflower: "sunflower {}" 
  by (rule card2_sunflower, auto)

lemma singleton_sunflower: "sunflower {A}" 
  by (rule card2_sunflower, auto)

lemma doubleton_sunflower: "sunflower {A,B}" 
  by (rule card2_sunflower, auto, cases "A = B", auto)

lemma sunflower_imp_union_intersect_unique: 
  assumes "sunflower S"
    and "x \<in> (\<Union> S) - (\<Inter> S)" 
  shows "\<exists>! A. A \<in> S \<and> x \<in> A"
proof -
  from assms obtain A where A: "A \<in> S" "x \<in> A" by auto
  show ?thesis
  proof
    show "A \<in> S \<and> x \<in> A" using A by auto
    fix B 
    assume B: "B \<in> S \<and> x \<in> B" 
    show "B = A" 
    proof (rule ccontr)
      assume "B \<noteq> A" 
      with A B have "\<exists>A B. A \<in> S \<and> B \<in> S \<and> A \<noteq> B \<and> x \<in> A \<and> x \<in> B" by auto
      from \<open>sunflower S\<close>[unfolded sunflower_def, rule_format, OF this]
      have "x \<in> \<Inter> S" by auto
      with assms show False by auto
    qed
  qed
qed

lemma union_intersect_unique_imp_sunflower: 
  assumes "\<And> x. x \<in> (\<Union> S) - (\<Inter> S) \<Longrightarrow> \<exists>\<^sub>\<le>\<^sub>1 A. A \<in> S \<and> x \<in> A" 
  shows "sunflower S"
  unfolding sunflower_def
proof (intro allI impI, elim exE conjE, goal_cases)
  case (1 x C A B)
  hence x: "x \<in> \<Union> S" by auto
  show ?case
  proof (cases "x \<in> \<Inter> S")
    case False
    with assms[of x] x have "\<exists>\<^sub>\<le>\<^sub>1 A. A \<in> S \<and> x \<in> A" by blast
    with 1 have False unfolding Uniq_def by blast
    thus ?thesis ..
  next
    case True
    with 1 show ?thesis by blast
  qed
qed

lemma sunflower_iff_union_intersect_unique: 
  "sunflower S \<longleftrightarrow> (\<forall> x \<in> \<Union> S - \<Inter> S. \<exists>! A. A \<in> S \<and> x \<in> A)" 
  (is "?l = ?r")
proof 
  assume ?l
  from sunflower_imp_union_intersect_unique[OF this]
  show ?r by auto
next
  assume ?r
  hence *: "\<forall>x\<in>\<Union> S - \<Inter> S. \<exists>\<^sub>\<le>\<^sub>1 A. A \<in> S \<and> x \<in> A" 
    unfolding ex1_iff_ex_Uniq by auto
  show ?l
    by (rule union_intersect_unique_imp_sunflower, insert *, auto)
qed

lemma sunflower_iff_intersect_Uniq: 
  "sunflower S \<longleftrightarrow> (\<forall> x.  x \<in> \<Inter> S \<or> (\<exists>\<^sub>\<le>\<^sub>1 A. A \<in> S \<and> x \<in> A))" 
  (is "?l = ?r")
proof 
  assume ?l
  from sunflower_imp_union_intersect_unique[OF this]
  show ?r unfolding ex1_iff_ex_Uniq
    by (metis (no_types, lifting) DiffI UnionI Uniq_I)
next
  assume ?r
  show ?l
    by (rule union_intersect_unique_imp_sunflower, insert \<open>?r\<close>, auto)
qed

text \<open>If there exists sunflowers whenever all elements are sets of 
  the same cardinality @{term r}, then there also exists sunflowers 
  whenever all elements are sets with cardinality at most @{term r}.\<close>

lemma sunflower_card_subset_lift: fixes F :: "'a set set" 
  assumes sunflower: "\<And> G :: ('a + nat) set set. 
     (\<forall> A \<in> G. finite A \<and> card A = k) \<Longrightarrow> card G > c 
        \<Longrightarrow> \<exists> S. S \<subseteq> G \<and> sunflower S \<and> card S = r" 
    and kF: "\<forall> A \<in> F. finite A \<and> card A \<le> k"
    and cardF: "card F > c"
  shows "\<exists> S. S \<subseteq> F \<and> sunflower S \<and> card S = r" 
proof -
  let ?n = "Suc c" 
  from cardF have "card F \<ge> ?n" by auto
  then obtain FF where sub: "FF \<subseteq> F" and cardF: "card FF = ?n" 
    by (rule obtain_subset_with_card_n)
  let ?N = "{0 ..< ?n}" 
  from cardF have "finite FF" 
    by (simp add: card_ge_0_finite)
  from ex_bij_betw_nat_finite[OF this, unfolded cardF]
  obtain f where f: "bij_betw f ?N FF" by auto
  hence injf: "inj_on f ?N" by (rule bij_betw_imp_inj_on)
  have Ff: "FF = f ` ?N"
    by (metis bij_betw_imp_surj_on f)
  define g where "g = (\<lambda> i. (Inl ` f i) \<union> (Inr ` {0 ..< (k - card (f i))}))" 
  have injg: "inj_on g ?N" unfolding g_def using f
  proof (intro inj_onI, goal_cases)
    case (1 x y)
    hence "f x = f y" by auto
    with injf 1 show "x = y" 
      by (meson inj_onD)
  qed
  hence cardgN: "card (g ` ?N) > c" 
    by (simp add: card_image)
  {
    fix i
    assume "i \<in> ?N" 
    hence "f i \<in> FF" unfolding Ff by auto
    with sub have "f i \<in> F" by auto
    hence "card (f i) \<le> k" "finite (f i)" using kF by auto
    hence "card (g i) = k \<and> finite (g i)" unfolding g_def
      by (subst card_Un_disjoint, auto, subst (1 2) card_image, auto intro: inj_onI)
  }
  hence "\<forall> A \<in> g ` ?N. finite A \<and> card A = k" by auto
  from sunflower[OF this cardgN]
  obtain S where SgN: "S \<subseteq> g ` ?N" and sf: "sunflower S" and card: "card S = r" by auto
  from SgN obtain N where NN: "N \<subseteq> ?N" and SgN: "S = g ` N"
    by (meson subset_image_iff)
  from injg NN have inj_g: "inj_on g N"
    by (rule inj_on_subset)
  from injf NN have inj_f: "inj_on f N"
    by (rule inj_on_subset)
  from card_image[OF inj_g] SgN card
  have cardN: "card N = r" by auto
  let ?S = "f ` N" 
  show ?thesis
  proof (intro exI[of _ ?S] conjI)
    from NN show "?S \<subseteq> F" using Ff sub by auto
    from card_image[OF inj_f] cardN show "card ?S = r" by auto
    show "sunflower ?S" unfolding sunflower_def
    proof (intro allI impI, elim exE conjE, goal_cases)
      case (1 x C A B)
      from \<open>A \<in> f ` N\<close> obtain i where i: "i \<in> N" and A: "A = f i" by auto
      from \<open>B \<in> f ` N\<close> obtain j where j: "j \<in> N" and B: "B = f j" by auto
      from \<open>C \<in> f ` N\<close> obtain k where k: "k \<in> N" and C: "C = f k" by auto
      hence gk: "g k \<in> g ` N" by auto
      from \<open>A \<noteq> B\<close> A B have ij: "i \<noteq> j" by auto
      from inj_g ij i j have gij: "g i \<noteq> g j" by (metis inj_on_contraD)
      from \<open>x \<in> A\<close> have memi: "Inl x \<in> g i" unfolding A g_def by auto
      from \<open>x \<in> B\<close> have memj: "Inl x \<in> g j" unfolding B g_def by auto
      have "\<exists>A B. A \<in> g ` N \<and> B \<in> g ` N \<and> A \<noteq> B \<and> Inl x \<in> A \<and> Inl x \<in> B" 
        using memi memj gij i j by auto
      from sf[unfolded sunflower_def SgN, rule_format, OF this gk] have "Inl x \<in> g k" .
      thus "x \<in> C" unfolding C g_def by auto
    qed
  qed
qed

text \<open>We provide another sunflower lifting lemma that ensures 
  non-empty cores. Here, all elements must be taken 
  from a finite set, and the bound is multiplied the cardinality.\<close>

lemma sunflower_card_core_lift: 
  assumes finE: "finite (E :: 'a set)" 
    and sunflower: "\<And> G :: 'a set set. 
     (\<forall> A \<in> G. finite A \<and> card A \<le> k) \<Longrightarrow> card G > c 
        \<Longrightarrow> \<exists> S. S \<subseteq> G \<and> sunflower S \<and> card S = r" 
    and F: "\<forall> A \<in> F. A \<subseteq> E \<and> s \<le> card A \<and> card A \<le> k" 
    and cardF: "card F > (card E choose s) * c"
    and s: "s \<noteq> 0"
    and r: "r \<noteq> 0" 
  shows "\<exists> S. S \<subseteq> F \<and> sunflower S \<and> card S = r \<and> card (\<Inter> S) \<ge> s"
proof -
  let ?g = "\<lambda> (A :: 'a set) x. card x = s \<and> x \<subseteq> A" 
  let ?E = "{X. X \<subseteq> E \<and> card X = s}"
  from cardF have finF: "finite F"
    by (metis card.infinite le_0_eq less_le)
  from cardF have FnE: "F \<noteq> {}" by force
  {
    from FnE obtain B where B: "B \<in> F" by auto
    with F[rule_format, OF B] obtain A where "A \<subseteq> E" "card A = s"
      by (meson obtain_subset_with_card_n order_trans)
    hence "?E \<noteq> {}" using B by auto
  } note EnE = this
  define f where "f = (\<lambda> A. SOME x. ?g A x)" 
  from finE have finiteE: "finite ?E" by simp
  
  have "f \<in> F \<rightarrow> ?E"
  proof
    fix B
    assume B: "B \<in> F" 
    with F[rule_format, OF B] have "\<exists> x. ?g B x" by (meson obtain_subset_with_card_n)
    from someI_ex[OF this] B F show "f B \<in> ?E" unfolding f_def by auto
  qed
  from pigeonhole_card[OF this finF finiteE EnE]
  obtain a where a: "a \<in> ?E" 
    and le: "card F \<le> card (f -` {a} \<inter> F) * card ?E" by auto
  have precond: "\<forall>A\<in>f -` {a} \<inter> F. finite A \<and> card A \<le> k" 
    using F finite_subset[OF _ finE] by auto
  have "c * (card E choose s) = (card E choose s) * c" by simp
  also have "\<dots> < card F" by fact
  also have "\<dots> \<le> (card (f -` {a} \<inter> F)) * card ?E" by fact
  also have "card ?E = card E choose s" by (rule n_subsets[OF finE])
  finally have "c < card (f -` {a} \<inter> F)" by auto
  from sunflower[OF precond this]
  obtain S where *: "S \<subseteq> f -` {a} \<inter> F" "sunflower S" "card S = r"
    by auto
  from finite_subset[OF _ finF, of S] 
  have finS: "finite S" using * by auto
  from * r have SnE: "S \<noteq> {}" by auto
  have finIS: "finite (\<Inter> S)" 
  proof (rule finite_Inter)
    from SnE obtain A where A: "A \<in> S" by auto
    with F s have "finite A"
      using * precond by blast
    thus "\<exists>A\<in>S. finite A" using A by auto
  qed
  show ?thesis
  proof (intro exI[of _ S] conjI *)
    show "S \<subseteq> F" using * by auto
    {
      fix A
      assume "A \<in> S" 
      with *(1) have "A \<in> f -` {a}" and A: "A \<in> F" using * by auto
      from this have **: "f A = a" "A \<in> F" by auto
      from F[rule_format, OF A] have "\<exists>x. card x = s \<and> x \<subseteq> A" 
        by (meson obtain_subset_with_card_n order_trans)
      from someI_ex[of "?g A", OF this] **
      have "a \<subseteq> A" unfolding f_def by auto
    }
    hence "a \<subseteq> \<Inter> S" by auto
    from card_mono[OF finIS this] 
    have "card a \<le> card (\<Inter> S)" .
    with a show "s \<le> card (\<Inter> S)" by auto
  qed
qed

lemma sunflower_nonempty_core_lift: 
  assumes finE: "finite (E :: 'a set)" 
    and sunflower: "\<And> G :: 'a set set. 
     (\<forall> A \<in> G. finite A \<and> card A \<le> k) \<Longrightarrow> card G > c 
        \<Longrightarrow> \<exists> S. S \<subseteq> G \<and> sunflower S \<and> card S = r" 
    and F: "\<forall> A \<in> F. A \<subseteq> E \<and> card A \<le> k" 
    and empty: "{} \<notin> F" 
    and cardF: "card F > card E * c"
  shows "\<exists> S. S \<subseteq> F \<and> sunflower S \<and> card S = r \<and> (\<Inter> S) \<noteq> {}"
proof (cases "r = 0")
  case False
  from F empty have F': "\<forall>A\<in>F. A \<subseteq> E \<and> 1 \<le> card A \<and> card A \<le> k " using finE
    by (metis One_nat_def Suc_leI card_gt_0_iff finite_subset)
  from cardF have cardF': "(card E choose 1) * c < card F" by auto
  from sunflower_card_core_lift[OF finE sunflower, of k c F 1, OF _ _ F' cardF' _ False]
  obtain S where "S \<subseteq> F" and main: "sunflower S" "card S = r" "1 \<le> card (\<Inter> S)" by auto
  thus ?thesis by (intro exI[of _ S], auto)
next
  case True
  thus ?thesis by (intro exI[of _ "{}"], auto simp: empty_sunflower)
qed


end 