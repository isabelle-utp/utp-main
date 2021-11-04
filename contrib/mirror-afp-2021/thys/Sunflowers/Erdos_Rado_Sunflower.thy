(* author: R. Thiemann *)

section \<open>The Sunflower Lemma\<close>

text \<open>We formalize the proof of the sunflower lemma of Erdős and Rado~\cite{erdos_rado}, 
as it is presented in the textbook~\cite[Chapter~6]{book}.  
We further integrate Exercise 6.2 from the textbook,
which provides a lower bound on the existence of sunflowers.\<close>

theory Erdos_Rado_Sunflower
  imports 
    Sunflower
begin

text \<open>When removing an element from all subsets, then one can afterwards
  add these elements to a sunflower and get a new sunflower.\<close>

lemma sunflower_remove_element_lift: 
  assumes S: "S \<subseteq> { A - {a} | A . A \<in> F \<and> a \<in> A}" 
    and sf: "sunflower S" 
  shows "\<exists> Sa. sunflower Sa \<and> Sa \<subseteq> F \<and> card Sa = card S \<and> Sa = insert a ` S" 
proof (intro exI[of _ "insert a ` S"] conjI refl)
  let ?Sa = "insert a ` S" 
  {
    fix B
    assume "B \<in> ?Sa" 
    then obtain C where C: "C \<in> S" and B: "B = insert a C" 
      by auto
    from C S obtain T where "T \<in> F" "a \<in> T" "C = T - {a}" 
      by auto
    with B have "B = T" by auto
    with \<open>T \<in> F\<close> have "B \<in> F" by auto
  } 
  thus SaF: "?Sa \<subseteq> F" by auto
  have inj: "inj_on (insert a) S" using S 
    by (intro inj_on_inverseI[of _ "\<lambda> B. B - {a}"], auto)
  thus "card ?Sa = card S" by (rule card_image)
  show "sunflower ?Sa" unfolding sunflower_def
  proof (intro allI, intro impI)
    fix x
    assume "\<exists>C D. C \<in> ?Sa \<and> D \<in> ?Sa \<and> C \<noteq> D \<and> x \<in> C \<and> x \<in> D"
    then obtain C D where *: "C \<in> ?Sa" "D \<in> ?Sa" "C \<noteq> D" "x \<in> C" "x \<in> D" 
      by auto
    from *(1-2) obtain C' D' where 
      **: "C' \<in> S" "D' \<in> S" "C = insert a C'" "D = insert a D'" 
      by auto
    with \<open>C \<noteq> D\<close> inj have CD': "C' \<noteq> D'" by auto
    show "\<forall>E. E \<in> ?Sa \<longrightarrow> x \<in> E" 
    proof (cases "x = a")
      case False
      with * ** have "x \<in> C'" "x \<in> D'" by auto
      with ** CD' have "\<exists>C D. C \<in> S \<and> D \<in> S \<and> C \<noteq> D \<and> x \<in> C \<and> x \<in> D" by auto
      from sf[unfolded sunflower_def, rule_format, OF this]
      show ?thesis by auto
    qed auto
  qed
qed

text \<open>The sunflower-lemma of Erdős and Rado: 
  if a set has a certain size and all elements
  have the same cardinality, then a sunflower exists.\<close>

lemma Erdos_Rado_sunflower_same_card: 
  assumes "\<forall> A \<in> F. finite A \<and> card A = k" 
    and "card F > (r - 1)^k * fact k"
  shows "\<exists> S. S \<subseteq> F \<and> sunflower S \<and> card S = r \<and> {} \<notin> S" 
  using assms 
proof (induct k arbitrary: F)
  case 0
  hence "F = {{}} \<or> F = {}" "card F \<ge> 2" by auto
  hence False by auto
  thus ?case by simp
next 
  case (Suc k F)
  define pd_sub :: "'a set set \<Rightarrow> nat \<Rightarrow> bool" where
    "pd_sub = (\<lambda> G t. G \<subseteq> F \<and> card G = t \<and> pairwise disjnt G \<and> {} \<notin> G)"
  show ?case
  proof (cases "\<exists> t G. pd_sub G t \<and> t \<ge> r")
    case True
    then obtain t G where pd_sub: "pd_sub G t" and t: "t \<ge> r" by auto
    from pd_sub[unfolded pd_sub_def] pairwise_disjnt_imp_sunflower
    have *: "G \<subseteq> F" "card G = t" "sunflower G" "{} \<notin> G" by auto
    from t \<open>card G = t\<close> obtain H where "H \<subseteq> G" "card H = r"
      by (metis obtain_subset_with_card_n)
    with sunflower_subset[OF \<open>H \<subseteq> G\<close>] * show ?thesis by blast
  next
    case False
    define P where "P = (\<lambda> t. \<exists> G. pd_sub G t)" 
    have ex: "\<exists> t. P t" unfolding P_def
      by (intro exI[of _ 0] exI[of _ "{}"], auto simp: pd_sub_def)
    have large': "\<And> t. P t \<Longrightarrow> t < r" using False unfolding P_def by auto
    hence large: "\<And> t. P t \<Longrightarrow> t \<le> r" by fastforce 
    define t where "t = (GREATEST t. P t)"
    from GreatestI_ex_nat[OF ex large, folded t_def] have Pt: "P t" .
    from Greatest_le_nat[of P, OF _ large] 
    have greatest: "\<And> s. P s \<Longrightarrow> s \<le> t" unfolding t_def by auto
    from large'[OF Pt] have tr: "t \<le> r - 1" by simp
    from Pt[unfolded P_def pd_sub_def] obtain G where 
      cardG: "card G = t" and 
      disj: "pairwise disjnt G" and 
      GF: "G \<subseteq> F" 
      by blast
    define A where "A = (\<Union> G)"
    from Suc(3) have "card F > 0" by simp
    hence "finite F" by (rule card_ge_0_finite)
    from GF \<open>finite F\<close> have finG: "finite G" by (rule finite_subset)
    have "card (\<Union> G) \<le> sum card G" 
      by (rule card_Union_le_sum_card, insert Suc(2) GF, auto)
    also have "\<dots> \<le> of_nat (card G) * Suc k" 
      by (rule sum_bounded_above, insert GF Suc(2), auto)
    also have "\<dots> \<le> (r - 1) * Suc k" 
      using tr[folded cardG] by (metis id_apply mult_le_mono1 of_nat_eq_id)
    finally have cardA: "card A \<le> (r - 1) * Suc k" unfolding A_def .
    {
      fix B
      assume *: "B \<in> F"
      with Suc(2) have nE: "B \<noteq> {}" by auto
      from Suc(2) have eF: "{} \<notin> F" by auto
      have "B \<inter> A \<noteq> {}"
      proof
        assume dis: "B \<inter> A = {}"
        hence disj: "pairwise disjnt ({B} \<union> G)"  using disj unfolding A_def
          by (smt (verit, ccfv_SIG) Int_commute Un_iff 
              Union_disjoint disjnt_def pairwise_def singleton_iff)
        from nE dis have "B \<notin> G" unfolding A_def by auto
        with finG have c: "card ({B} \<union> G) = Suc t" by (simp add: cardG)
        have "P (Suc t)" unfolding P_def pd_sub_def
          by (intro exI[of _ "{B} \<union> G"], insert eF disj c * GF, auto)
        with greatest show False by force
      qed
    } note overlap = this
    have "F \<noteq> {}" using Suc(2-) by auto
    with overlap have Ane: "A \<noteq> {}" unfolding A_def by auto
    have "finite A" unfolding A_def using finG Suc(2-) GF by auto
    let ?g = "\<lambda> B x. x \<in> B \<inter> A" 
    define f where "f = (\<lambda> B. SOME x. ?g B x)" 
    have "f \<in> F \<rightarrow> A"
    proof
      fix B
      assume "B \<in> F" 
      from overlap[OF this] have "\<exists> x. ?g B x" unfolding A_def by auto
      from someI_ex[OF this] show "f B \<in> A" unfolding f_def by auto
    qed
    from pigeonhole_card[OF this \<open>finite F\<close> \<open>finite A\<close> Ane]
    obtain a where a: "a \<in> A" 
      and le: "card F \<le> card (f -` {a} \<inter> F) * card A" by auto
    {
      fix S 
      assume "S \<in> F" "f S \<in> {a}"
      with someI_ex[of "?g S"] a overlap[OF this(1)]
      have "a \<in> S" unfolding f_def by auto
    } note FaS = this
    let ?F = "{S - {a} | S . S \<in> F \<and> f S \<in> {a}}" 
    from cardA have "((r - 1) ^ k * fact k) * card A \<le> ((r - 1) ^ k * fact k) * ((r - 1) * Suc k)"
      by simp
    also have "\<dots> = (r - 1) ^ (Suc k) * fact (Suc k)"
      by (metis (no_types, lifting) fact_Suc mult.assoc mult.commute of_nat_id power_Suc2)
    also have "\<dots> < card (f -` {a} \<inter> F) * card A" 
      using Suc(3) le by auto
    also have "f -` {a} \<inter> F = {S \<in> F. f S \<in> {a}}" by auto
    also have "card \<dots> = card ((\<lambda> S. S - {a}) ` {S \<in> F. f S \<in> {a}})" 
      by (subst card_image; intro inj_onI refl, insert FaS) auto
    also have "(\<lambda> S. S - {a}) ` {S \<in> F. f S \<in> {a}} = ?F" by auto
    finally have lt: "(r - 1) ^ k * fact k < card ?F" by simp
    have "\<forall> A \<in> ?F. finite A \<and> card A = k" using Suc(2) FaS by auto
    from Suc(1)[OF this lt] obtain S
      where "sunflower S" "card S = r" "S \<subseteq> ?F" by auto
    from \<open>S \<subseteq> ?F\<close> FaS have "S \<subseteq> {A - {a} |A. A \<in> F \<and> a \<in> A}" by auto
    from sunflower_remove_element_lift[OF this \<open>sunflower S\<close>] \<open>card S = r\<close>
    show ?thesis by auto
  qed
qed

text \<open>Using @{thm [source] sunflower_card_subset_lift} we can easily 
  replace the condition that the cardinality is exactly @{term k}
  by the requirement that the cardinality is at most @{term k}. 
  However, then @{term "{} \<notin> S"} cannot be ensured.
  Consider @{term "(r :: nat) = 1 \<and> (k :: nat) > 0 \<and> F = {{}}"}.\<close>

lemma Erdos_Rado_sunflower: 
  assumes "\<forall> A \<in> F. finite A \<and> card A \<le> k" 
    and "card F > (r - 1)^k * fact k"
  shows "\<exists> S. S \<subseteq> F \<and> sunflower S \<and> card S = r" 
  by (rule sunflower_card_subset_lift[OF _ assms], 
      metis Erdos_Rado_sunflower_same_card)

text \<open>We further provide a lower bound on the existence of sunflowers, 
i.e., Exercise 6.2 of the textbook~\cite{book}.
To be more precise, we prove that there is a set of sets of cardinality 
@{term \<open>(r - 1 :: nat)^k\<close>}, where each element is a set of cardinality 
@{term k}, such that there is no subset which is a sunflower with cardinality
of at least @{term r}.\<close>

lemma sunflower_lower_bound:
  assumes inf: "infinite (UNIV :: 'a set)" 
    and r: "r \<noteq> 0"
    and rk: "r = 1 \<Longrightarrow> k \<noteq> 0" 
  shows "\<exists> F. 
    card F = (r - 1)^k \<and> finite F \<and>
    (\<forall> A \<in> F. finite (A :: 'a set) \<and> card A = k) \<and>
    (\<nexists> S. S \<subseteq> F \<and> sunflower S \<and> card S \<ge> r)" 
proof (cases "r = 1")
  case False
  with r have r: "r > 1" by auto
  show ?thesis
  proof (induct k)
    case 0
    have id: "S \<subseteq> {{}} \<longleftrightarrow> (S = {} \<or> S = {{}})" for S :: "'a set set" by auto 
    show ?case using r
      by (intro exI[of _ "{{}}"], auto simp: id)
  next
    case (Suc k)
    then obtain F where
      cardF: "card F = (r - 1) ^ k" and
      fin: "finite F" and
      AF: "\<And> A. (A :: 'a set) \<in> F \<Longrightarrow> finite A \<and> card A = k" and
      sf: "\<not> (\<exists>S\<subseteq>F. sunflower S \<and> r \<le> card S)" 
      by metis
    text \<open>main idea: get @{term "k-1 :: nat"} fresh elements 
      and add one of these to all elements of F\<close>
    have "finite (\<Union> F)" using fin AF by simp
    hence "infinite (UNIV - \<Union> F)" using inf by simp
    from infinite_arbitrarily_large[OF this, of "r - 1"]
    obtain New where New: "finite New" "card New = r - 1" 
      "New \<inter> \<Union> F = {}" by auto
    define G where "G = (\<lambda> (A, a). insert a A) ` (F \<times> New)" 
    show ?case
    proof (intro exI[of _ G] conjI)
      show "finite G" using New fin unfolding G_def by simp
      have "card G = card (F \<times> New)" unfolding G_def
      proof ((subst card_image; (intro refl)?), intro inj_onI, clarsimp, goal_cases)
        case (1 A a B b)
        hence ab: "a = b" using New by auto
        from 1(1) have "insert a A - {a} = insert b B - {a}" by simp
        also have "insert a A - {a} = A" using New 1 by auto
        also have "insert b B - {a} = B" using New 1 ab[symmetric] by auto
        finally show ?case using ab by auto
      qed
      also have "\<dots> = card F * card New" using New fin by auto
      finally show "card G = (r - 1) ^ Suc k" 
        unfolding cardF New by simp
      {
        fix B
        assume "B \<in> G" 
        then obtain a A where G: "a \<in> New" "A \<in> F" "B = insert a A" 
          unfolding G_def by auto
        with AF[of A] New have "finite B" "card B = Suc k" 
          by (auto simp: card_insert_if)
      }
      thus "\<forall>A\<in>G. finite A \<and> card A = Suc k" by auto
      show "\<not> (\<exists>S\<subseteq>G. sunflower S \<and> r \<le> card S)" 
      proof (intro notI, elim exE conjE)
        fix S
        assume *: "S \<subseteq> G" "sunflower S" "r \<le> card S"
        define g where "g B = (SOME a. a \<in> New \<and> a \<in> B)" for B
        {
          fix B
          assume "B \<in> S" 
          with \<open>S \<subseteq> G\<close> have "B \<in> G" by auto
          hence "\<exists> a. a \<in> New \<and> a \<in> B" unfolding G_def by auto
          from someI_ex[OF this, folded g_def]
          have "g B \<in> New" "g B \<in> B" by auto
        } note gB = this
        have "card (g ` S) \<le> card New" 
          by (rule card_mono, insert New gB, auto)
        also have "\<dots> < r" unfolding New using r by simp
        also have "\<dots> \<le> card S" by fact
        finally have "card (g ` S) < card S" .
        from pigeonhole[OF this] have "\<not> inj_on g S" .
        then obtain B1 B2 where B12: "B1 \<in> S" "B2 \<in> S" "B1 \<noteq> B2" "g B1 = g B2" 
          unfolding inj_on_def by auto
        define a where "a = g B2" 
        from B12 gB[of B1] gB[of B2] have a: "a \<in> New" "a \<in> B1" "a \<in> B2"
          unfolding a_def by auto  
        with B12 have "\<exists>B1 B2. B1 \<in> S \<and> B2 \<in> S \<and> B1 \<noteq> B2 \<and> a \<in> B1 \<and> a \<in> B2" 
          unfolding a_def by blast
        from \<open>sunflower S\<close>[unfolded sunflower_def, rule_format, OF this]
        have aS: "B \<in> S \<Longrightarrow> a \<in> B" for B by auto
        define h where "h B = B - {a}" for B
        define T where "T = h ` S" 
        have "\<exists>S\<subseteq>F. sunflower S \<and> r \<le> card S" 
        proof (intro exI[of _ T] conjI)
          {
            fix B
            assume "B \<in> S" 
            have hB: "h B = B - {a}" 
              unfolding h_def T_def by auto
            from aS \<open>B \<in> S\<close> have aB: "a \<in> B" by auto
            from \<open>B \<in> S\<close> \<open>S \<subseteq> G\<close> obtain a' A where AF: "A \<in> F" 
              and B: "B = insert a' A" 
              and a': "a' \<in> New" unfolding G_def by force
            from aB B a' New AF a(1) hB AF have "insert a (h B) = B" "h B = A" by auto
            hence "insert a (h B) = B" "h B \<in> F" "insert a (h B) \<in> S" using AF \<open>B \<in> S\<close> by auto
          } note main = this
          have CTS: "C \<in> T \<Longrightarrow> insert a C \<in> S" for C using main unfolding T_def by force
          show "T \<subseteq> F" unfolding T_def using main by auto
          have "r \<le> card S" by fact
          also have "\<dots> = card T" unfolding T_def
            by (subst card_image, intro inj_on_inverseI[of _ "insert a"], insert main, auto)
          finally show "r \<le> card T" .
          show "sunflower T" unfolding sunflower_def
          proof (intro allI impI, elim exE conjE, goal_cases)
            case (1 x C C1 C2)
            from CTS[OF \<open>C1 \<in> T\<close>] CTS[OF \<open>C2 \<in> T\<close>] CTS[OF \<open>C \<in> T\<close>]
            have *: "insert a C1 \<in> S" "insert a C2 \<in> S" "insert a C \<in> S" by auto          
            from 1 have "insert a C1 \<noteq> insert a C2" using main
              unfolding T_def by auto
            hence "\<exists>A B. A \<in> S \<and> B \<in> S \<and> A \<noteq> B \<and> x \<in> A \<and> x \<in> B" 
              using * 1 by auto          
            from \<open>sunflower S\<close>[unfolded sunflower_def, rule_format, OF this *(3)]
            have "x \<in> insert a C" .
            with 1 show "x \<in> C" unfolding T_def h_def by auto
          qed
        qed
        with sf
        show False ..
      qed
    qed
  qed
next
  case r: True
  with rk have "k \<noteq> 0" by auto
  then obtain l where k: "k = Suc l" by (cases k, auto)
  show ?thesis unfolding r k
    by (intro exI[of _ "{}"], auto)
qed

text \<open>The difference between the lower and the
upper bound on the existence of sunflowers as they have been formalized
is @{term \<open>fact k\<close>}. There is more recent work with tighter bounds
\cite{sunflower_new}, but we only integrate the initial 
result of Erdős and Rado in this theory.\<close>

text \<open>We further provide the Erdős Rado lemma 
  lifted to obtain non-empty cores or cores of arbitrary cardinality.\<close>

lemma Erdos_Rado_sunflower_card_core: 
  assumes "finite E" 
    and "\<forall> A \<in> F. A \<subseteq> E \<and> s \<le> card A \<and> card A \<le> k" 
    and "card F > (card E choose s) * (r - 1)^k * fact k"
    and "s \<noteq> 0" 
    and "r \<noteq> 0" 
  shows "\<exists> S. S \<subseteq> F \<and> sunflower S \<and> card S = r \<and> card (\<Inter> S) \<ge> s" 
  by (rule sunflower_card_core_lift[OF assms(1) _ assms(2) _ assms(4-5), 
        of "(r - 1)^k * fact k"],
      rule Erdos_Rado_sunflower, insert assms(3), auto simp: ac_simps)

lemma Erdos_Rado_sunflower_nonempty_core: 
  assumes "finite E" 
    and "\<forall> A \<in> F. A \<subseteq> E \<and> card A \<le> k" 
    and "{} \<notin> F" 
    and "card F > card E * (r - 1)^k * fact k"
  shows "\<exists> S. S \<subseteq> F \<and> sunflower S \<and> card S = r \<and> \<Inter> S \<noteq> {}" 
  by (rule sunflower_nonempty_core_lift[OF assms(1) 
      _ assms(2-3), of "(r - 1)^k * fact k"],
      rule Erdos_Rado_sunflower, insert assms(4), auto simp: ac_simps)

end 