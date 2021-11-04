(*
    File:     Finite_Product_Extend.thy
    Author:   Joseph Thommes, TU München; Manuel Eberl, TU München
*)
section \<open>Finite Product\<close>

theory Finite_Product_Extend
  imports IDirProds
begin

text \<open>In this section, some general facts about \<open>finprod\<close> as well as some tailored for the rest of
this entry are proven.\<close>

text \<open>It is often needed to split a product in a single factor and the rest. Thus these two lemmas.\<close>

lemma (in comm_group) finprod_minus:
  assumes "a \<in> A" "f \<in> A \<rightarrow> carrier G" "finite A"
  shows "finprod G f A = f a \<otimes> finprod G f (A - {a})"
proof -
  from assms have "A = insert a (A - {a})" by blast
  then have "finprod G f A = finprod G f (insert a (A - {a}))" by simp
  also have "\<dots> = f a \<otimes> finprod G f (A - {a})" using assms by (intro finprod_insert, auto)
  finally show ?thesis .
qed

lemma (in comm_group) finprod_minus_symm:
  assumes "a \<in> A" "f \<in> A \<rightarrow> carrier G" "finite A"
  shows "finprod G f A = finprod G f (A - {a}) \<otimes> f a"
proof -
  from assms have "A = insert a (A - {a})" by blast
  then have "finprod G f A = finprod G f (insert a (A - {a}))" by simp
  also have "\<dots> = f a \<otimes> finprod G f (A - {a})" using assms by (intro finprod_insert, auto)
  also have "\<dots> = finprod G f (A - {a}) \<otimes> f a"
    by (intro m_comm, use assms in blast, intro finprod_closed, use assms in blast)
  finally show ?thesis .
qed

text \<open>This makes it very easy to show the following trivial fact.\<close>

lemma (in comm_group) finprod_singleton:
  assumes "f x \<in> carrier G" "finprod G f {x} = a"
  shows "f x = a"
proof -
  have "finprod G f {x} = f x \<otimes> finprod G f {}" using finprod_minus[of x "{x}" f] assms by auto
  thus ?thesis using assms by simp
qed

text \<open>The finite product is consistent and closed concerning subgroups.\<close>

lemma (in comm_group) finprod_subgroup:
  assumes "f \<in> S \<rightarrow> H" "subgroup H G"
  shows "finprod G f S = finprod (G\<lparr>carrier := H\<rparr>) f S"
proof (cases "finite S")
  case True
  interpret H: comm_group "G\<lparr>carrier := H\<rparr>" using subgroup_is_comm_group[OF assms(2)] .
  show ?thesis using True assms
  proof (induction S rule: finite_induct)
    case empty
    then show ?case using finprod_empty H.finprod_empty by simp
  next
    case i: (insert x F)
    then have "finprod G f F = finprod (G\<lparr>carrier := H\<rparr>) f F" by blast
    moreover have "finprod G f (insert x F) = f x \<otimes> finprod G f F"
    proof(intro finprod_insert[OF i(1, 2), of f])
      show "f \<in> F \<rightarrow> carrier G" "f x \<in> carrier G" using i(4) subgroup.subset[OF i(5)] by blast+
    qed
    ultimately have "finprod G f (insert x F) = f x \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> finprod (G\<lparr>carrier := H\<rparr>) f F"
      by auto
    moreover have "finprod (G\<lparr>carrier := H\<rparr>) f (insert x F) = \<dots>"
    proof(intro H.finprod_insert[OF i(1, 2)])
      show "f \<in> F \<rightarrow> carrier (G\<lparr>carrier := H\<rparr>)" "f x \<in> carrier (G\<lparr>carrier := H\<rparr>)" using i(4) by auto
    qed
    ultimately show ?case by simp
  qed
next
  case False
  then show ?thesis unfolding finprod_def by simp
qed

lemma (in comm_group) finprod_closed_subgroup:
  assumes "subgroup H G" "f \<in> A \<rightarrow> H"
  shows "finprod G f A \<in> H"
  using assms(2)
proof (induct A rule: infinite_finite_induct)
case (infinite A)
then show ?case using subgroup.one_closed[OF assms(1)] by auto
next
  case empty
  then show ?case using subgroup.one_closed[OF assms(1)] by auto
next
  case i: (insert x F)
  from finprod_insert[OF i(1, 2), of f] i have fi: "finprod G f (insert x F) = f x \<otimes> finprod G f F"
    using subgroup.subset[OF assms(1)] by blast
  from i have "finprod G f F \<in> H" "f x \<in> H" by blast+
  with fi show ?case using subgroup.m_closed[OF assms(1)] by presburger 
qed

text \<open>It also does not matter if we exponentiate all elements taking part in the product or the
result of the product.\<close>

lemma (in comm_group) finprod_exp:
  assumes "A \<subseteq> carrier G" "f \<in> A \<rightarrow> carrier G"
  shows "(finprod G f A) [^] (k::int) = finprod G ((\<lambda>a. a [^] k) \<circ> f) A"
  using assms
proof(induction A rule: infinite_finite_induct)
  case i: (insert x F)
  hence ih: "finprod G f F [^] k = finprod G ((\<lambda>a. a [^] k) \<circ> f) F" by blast
  have fpc: "finprod G f F \<in> carrier G" by (intro finprod_closed, use i in auto)
  have fxc: "f x \<in> carrier G" using i by auto
  have "finprod G f (insert x F) = f x \<otimes> finprod G f F" by (intro finprod_insert, use i in auto)
  hence "finprod G f (insert x F) [^] k = (f x \<otimes> finprod G f F) [^] k" by simp
  also have "\<dots> = f x [^] k \<otimes> finprod G f F [^] k" using fpc fxc int_pow_distrib by blast
  also have "\<dots> = ((\<lambda>a. a [^] k) \<circ> f) x \<otimes> finprod G ((\<lambda>a. a [^] k) \<circ> f) F" using ih by simp
  also have "\<dots> = finprod G ((\<lambda>a. a [^] k) \<circ> f) (insert x F)"
    by (intro finprod_insert[symmetric], use i in auto)
  finally show ?case .
qed auto

text \<open>Some lemmas concerning different combinations of functions in the usage of \<open>finprod\<close>.\<close>

lemma (in comm_group) finprod_cong_split:
  assumes "\<And>a. a \<in> A \<Longrightarrow> f a \<otimes> g a = h a"
  and "f \<in> A \<rightarrow> carrier G" "g \<in> A \<rightarrow> carrier G" "h \<in> A \<rightarrow> carrier G"
  shows "finprod G h A = finprod G f A \<otimes> finprod G g A" using assms
proof(induct A rule: infinite_finite_induct)
  case (infinite A)
  then show ?case by simp
next
  case empty
  then show ?case by simp
next
  case i: (insert x F)
  then have iH: "finprod G h F = finprod G f F \<otimes> finprod G g F" by fast
  have f: "finprod G f (insert x F) = f x \<otimes> finprod G f F"
    by (intro finprod_insert[OF i(1, 2), of f]; use i(5) in simp)
  have g: "finprod G g (insert x F) = g x \<otimes> finprod G g F"
    by (intro finprod_insert[OF i(1, 2), of g]; use i(6) in simp)
  have h: "finprod G h (insert x F) = h x \<otimes> finprod G h F"
    by (intro finprod_insert[OF i(1, 2), of h]; use i(7) in simp)  
  also have "\<dots> = h x \<otimes> (finprod G f F \<otimes> finprod G g F)" using iH by argo
  also have "\<dots> = f x \<otimes> g x \<otimes> (finprod G f F \<otimes> finprod G g F)" using i(4) by simp
  also have "\<dots> = f x \<otimes> finprod G f F \<otimes> (g x \<otimes> finprod G g F)" using m_comm m_assoc i(5-7) by simp
  also have "\<dots> = finprod G f (insert x F) \<otimes> finprod G g (insert x F)" using f g by argo
  finally show ?case .
qed

lemma (in comm_group) finprod_comp:
  assumes "inj_on g A" "(f \<circ> g) ` A \<subseteq> carrier G"
  shows "finprod G f (g ` A) = finprod G (f \<circ> g) A"
  using finprod_reindex[OF _ assms(1), of f] using assms(2) unfolding comp_def by blast

text \<open>The subgroup generated by a set of generators (in an abelian group) is exactly the set of
elements that can be written as a finite product using only powers of these elements.\<close>

lemma (in comm_group) generate_eq_finprod_PiE_image:
  assumes "finite gs" "gs \<subseteq> carrier G"
  shows "generate G gs = (\<lambda>x. finprod G x gs) ` Pi\<^sub>E gs (\<lambda>a. generate G {a})" (is "?g = ?fp")
proof
  show "?g \<subseteq> ?fp"
  proof
    fix x
    assume x: "x \<in> ?g"
    thus "x \<in> ?fp"
    proof (induction rule: generate.induct)
      case one
      show ?case
      proof
        let ?r = "restrict (\<lambda>_. \<one>) gs"
        show "?r \<in> (\<Pi>\<^sub>E a\<in>gs. generate G {a})" using generate.one by auto
        show "\<one> = finprod G ?r gs" by(intro finprod_one_eqI[symmetric], simp)
      qed
    next
      case g: (incl g)
      show ?case
      proof
        let ?r = "restrict ((\<lambda>_. \<one>)(g := g)) gs"
        show "?r \<in> (\<Pi>\<^sub>E a\<in>gs. generate G {a})" using generate.one generate.incl[of g "{g}" G]
          by fastforce
        show "g = finprod G ?r gs"
        proof -
          have "finprod G ?r gs = ?r g \<otimes> finprod G ?r (gs - {g})"
            by (intro finprod_minus, use assms g in auto)
          moreover have "?r g = g" using g by simp
          moreover have "finprod G ?r (gs - {g}) = \<one>" by(rule finprod_one_eqI; use g in simp)
          ultimately show ?thesis using assms g by auto
        qed
      qed
    next
      case g: (inv g)
      show ?case
      proof
        let ?r = "restrict ((\<lambda>_. \<one>)(g := inv g)) gs"
        show "?r \<in> (\<Pi>\<^sub>E a\<in>gs. generate G {a})" using generate.one generate.inv[of g "{g}" G]
          by fastforce
        show "inv g = finprod G ?r gs"
        proof -
          have "finprod G ?r gs = ?r g \<otimes> finprod G ?r (gs - {g})"
            by (intro finprod_minus, use assms g in auto)
          moreover have "?r g = inv g" using g by simp
          moreover have "finprod G ?r (gs - {g}) = \<one>" by(rule finprod_one_eqI; use g in simp)
          ultimately show ?thesis using assms g by auto
        qed
      qed
    next
      case gh: (eng g h)
      from gh obtain i where i: "i \<in> (\<Pi>\<^sub>E a\<in>gs. generate G {a})" "g = finprod G i gs" by blast
      from gh obtain j where j: "j \<in> (\<Pi>\<^sub>E a\<in>gs. generate G {a})" "h = finprod G j gs" by blast
      from i j have "g \<otimes> h = finprod G i gs \<otimes> finprod G j gs" by blast
      also have "\<dots> = finprod G (\<lambda>a. i a \<otimes> j a) gs"
      proof(intro finprod_multf[symmetric]; rule)
        fix x
        assume x: "x \<in> gs"
        have "i x \<in> generate G {x}" "j x \<in> generate G {x}"using i(1) j(1) x by blast+
        thus "i x \<in> carrier G" "j x \<in> carrier G" using generate_incl[of "{x}"] x assms(2) by blast+
      qed
      also have "\<dots> = finprod G (restrict (\<lambda>a. i a \<otimes> j a) gs) gs"
      proof(intro finprod_cong)
        have ip: "i g \<in> generate G {g}" if "g \<in> gs" for g using i that by auto
        have jp: "j g \<in> generate G {g}" if "g \<in> gs" for g using j that by auto
        have "i g \<otimes> j g \<in> generate G {g}" if "g \<in> gs" for g
          using generate.eng[OF ip[OF that] jp[OF that]] .
        thus "((\<lambda>a. i a \<otimes> j a) \<in> gs \<rightarrow> carrier G) = True" using generate_incl assms(2) by blast
      qed auto
      finally have "g \<otimes> h = finprod G (restrict (\<lambda>a. i a \<otimes> j a) gs) gs" .
      moreover have "(restrict (\<lambda>a. i a \<otimes> j a) gs) \<in> (\<Pi>\<^sub>E a\<in>gs. generate G {a})"
      proof -
        have ip: "i g \<in> generate G {g}" if "g \<in> gs" for g using i that by auto
        have jp: "j g \<in> generate G {g}" if "g \<in> gs" for g using j that by auto
        have "i g \<otimes> j g \<in> generate G {g}" if "g \<in> gs" for g
          using generate.eng[OF ip[OF that] jp[OF that]] .
        thus ?thesis by auto
      qed
      ultimately show ?case using i j by blast
    qed
  qed
  show "?fp \<subseteq> ?g"
  proof
    fix x
    assume x: "x \<in> ?fp"
    then obtain f where f: "f \<in> (Pi\<^sub>E gs (\<lambda>a. generate G {a}))" "x = finprod G f gs" by blast
    have sg: "subgroup ?g G" by(intro generate_is_subgroup, fact)
    have "finprod G f gs \<in> ?g"
    proof(intro finprod_closed_subgroup[OF sg])
      have "f g \<in> generate G gs" if "g \<in> gs" for g
      proof -
        have "f g \<in> generate G {g}" using f(1) that by auto
        moreover have "generate G {g} \<subseteq> generate G gs" by(intro mono_generate, use that in simp)
        ultimately show ?thesis by fast
      qed
      thus "f \<in> gs \<rightarrow> generate G gs" by simp
    qed
    thus "x \<in> ?g" using f by blast
  qed
qed

lemma (in comm_group) generate_eq_finprod_Pi_image:
  assumes "finite gs" "gs \<subseteq> carrier G"
  shows "generate G gs = (\<lambda>x. finprod G x gs) ` Pi gs (\<lambda>a. generate G {a})" (is "?g = ?fp")
proof -
  have "(\<lambda>x. finprod G x gs) ` Pi\<^sub>E gs (\<lambda>a. generate G {a})
      = (\<lambda>x. finprod G x gs) ` Pi gs (\<lambda>a. generate G {a})"
  proof
    have "Pi\<^sub>E gs (\<lambda>a. generate G {a}) \<subseteq> Pi gs (\<lambda>a. generate G {a})" by blast
    thus "(\<lambda>x. finprod G x gs) ` Pi\<^sub>E gs (\<lambda>a. generate G {a})
        \<subseteq> (\<lambda>x. finprod G x gs) ` Pi gs (\<lambda>a. generate G {a})" by blast
    show "(\<lambda>x. finprod G x gs) ` Pi gs (\<lambda>a. generate G {a})
        \<subseteq> (\<lambda>x. finprod G x gs) ` Pi\<^sub>E gs (\<lambda>a. generate G {a})"
    proof
      fix x
      assume x: "x \<in> (\<lambda>x. finprod G x gs) ` Pi gs (\<lambda>a. generate G {a})"
      then obtain f where f: "x = finprod G f gs" "f \<in> Pi gs (\<lambda>a. generate G {a})" by blast
      moreover have "finprod G f gs = finprod G (restrict f gs) gs"
      proof(intro finprod_cong)
        have "f g \<in> carrier G" if "g \<in> gs" for g
          using that f(2) mono_generate[of "{g}" gs] generate_incl[OF assms(2)] by fast
        thus "(f \<in> gs \<rightarrow> carrier G) = True" by blast
      qed auto        
      moreover have "restrict f gs \<in> Pi\<^sub>E gs (\<lambda>a. generate G {a})" using f(2) by simp
      ultimately show "x \<in> (\<lambda>x. finprod G x gs) ` Pi\<^sub>E gs (\<lambda>a. generate G {a})" by blast
    qed
  qed
  with generate_eq_finprod_PiE_image[OF assms] show ?thesis by auto
qed

lemma (in comm_group) generate_eq_finprod_Pi_int_image:
  assumes "finite gs" "gs \<subseteq> carrier G"
  shows "generate G gs = (\<lambda>x. finprod G (\<lambda>g. g [^] x g) gs) ` Pi gs (\<lambda>_. (UNIV::int set))"
proof -
  from generate_eq_finprod_Pi_image[OF assms]
  have "generate G gs = (\<lambda>x. finprod G x gs) ` (\<Pi> a\<in>gs. generate G {a})" .
  also have "\<dots> = (\<lambda>x. finprod G (\<lambda>g. g [^] x g) gs) ` Pi gs (\<lambda>_. (UNIV::int set))"
  proof(rule; rule)
    fix x
    assume x: "x \<in> (\<lambda>x. finprod G x gs) ` (\<Pi> a\<in>gs. generate G {a})"
    then obtain f where f: "f \<in> (\<Pi> a\<in>gs. generate G {a})" "x = finprod G f gs" by blast
    hence "\<exists>k::int. f a = a [^] k" if "a \<in> gs" for a using generate_pow[of a] that assms(2) by blast
    hence "\<exists>(h::'a \<Rightarrow> int). \<forall>a\<in>gs. f a = a [^] h a" by meson
    then obtain h where h: "\<forall>a\<in>gs. f a = a [^] h a" "h \<in> gs \<rightarrow> (UNIV :: int set)" by auto
    have "finprod G (\<lambda>g. g [^] h g) gs = finprod G f gs"
      by (intro finprod_cong, use int_pow_closed h assms(2) in auto)
    with f have "x = finprod G (\<lambda>g. g [^] h g) gs" by argo
    with h(2) show "x \<in> (\<lambda>x. finprod G (\<lambda>g. g [^] x g) gs) ` (gs \<rightarrow> (UNIV::int set))" by auto
  next
    fix x
    assume x: "x \<in> (\<lambda>x. finprod G (\<lambda>g. g [^] x g) gs) ` (gs \<rightarrow> (UNIV::int set))"
    then obtain h where h: "x = finprod G (\<lambda>g. g [^] h g) gs" "h \<in> gs \<rightarrow> (UNIV :: int set)" by blast
    hence "\<exists>k\<in>generate G {a}. a [^] h a = k" if "a \<in> gs" for a
      using generate_pow[of a] that assms(2) by blast
    then obtain f where f: "\<forall>a\<in>gs. a [^] h a = f a" "f \<in> (\<Pi> a\<in>gs. generate G {a})" by fast
    have "finprod G f gs = finprod G (\<lambda>g. g [^] h g) gs"
    proof(intro finprod_cong)
      have "f a \<in> carrier G" if "a \<in> gs" for a
        using generate_incl[of "{a}"] assms(2) that f(2) by fast
      thus "(f \<in> gs \<rightarrow> carrier G) = True" by blast
    qed (use f in auto)
    with h have "x = finprod G f gs" by argo
    with f(2) show "x \<in> (\<lambda>x. finprod G x gs) ` (\<Pi> a\<in>gs. generate G {a})" by blast
  qed
  finally show ?thesis .
qed


lemma (in comm_group) IDirProds_eq_finprod_PiE:
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> subgroup (S i) G"
  shows "IDirProds G S I = (\<lambda>x. finprod G x I) ` (Pi\<^sub>E I S)" (is "?DP = ?fp")
proof
  show "?fp \<subseteq> ?DP"
  proof
    fix x
    assume x: "x \<in> ?fp"
    then obtain f where f: "f \<in> (Pi\<^sub>E I S)" "x = finprod G f I" by blast
    have sDP: "subgroup ?DP G"
      by (intro IDirProds_is_subgroup; use subgroup.subset[OF assms(2)] in blast)
    have "finprod G f I \<in> ?DP"
    proof(intro finprod_closed_subgroup[OF sDP])
      have "f i \<in> IDirProds G S I" if "i \<in> I" for i
      proof
        show "f i \<in> (S i)" using f(1) that by auto
        show "(S i) \<subseteq> IDirProds G S I" by (intro IDirProds_incl[OF that])
      qed
      thus "f \<in> I \<rightarrow> IDirProds G S I" by simp
    qed
    thus "x \<in> ?DP" using f by blast
  qed
  show "?DP \<subseteq> ?fp"
  proof(unfold IDirProds_def; rule subsetI)
    fix x
    assume x: "x \<in> generate G (\<Union>(S ` I))"
    thus "x \<in> ?fp" using assms
    proof (induction rule: generate.induct)
      case one
      define g where g: "g = (\<lambda>x. if x \<in> I then \<one> else undefined)"
      then have "g \<in> Pi\<^sub>E I S"
        using subgroup.one_closed[OF one(2)] by auto
      moreover have "finprod G g I = \<one>" by (intro finprod_one_eqI; use g in simp)
      ultimately show ?case unfolding image_def by (auto; metis)
    next
      case i: (incl h)
      from i obtain j where j: "j \<in> I" "h \<in> (S j)" by blast
      define hf where "hf = (\<lambda>x. (if x \<in> I then \<one> else undefined))(j := h)"
      with j have "hf \<in> Pi\<^sub>E I S"
        using subgroup.one_closed[OF i(3)] by force
      moreover have "finprod G hf I = h"
      proof -
        have "finprod G hf I = hf j \<otimes> finprod G hf (I - {j})"
          by (intro finprod_minus, use assms hf_def subgroup.subset[OF i(3)[OF j(1)]] j in auto)
        moreover have "hf j = h" using hf_def by simp
        moreover have "finprod G hf (I - {j}) = \<one>" by (rule finprod_one_eqI; use hf_def in simp)
        ultimately show ?thesis using subgroup.subset[OF i(3)[OF j(1)]] j(2) by auto
      qed
      ultimately show ?case unfolding image_def by (auto; metis)
    next
      case i: (inv h)
      from i obtain j where j: "j \<in> I" "h \<in> (S j)" by blast
      have ih: "inv h \<in> (S j)" using subgroup.m_inv_closed[OF i(3)[OF j(1)] j(2)] .
      define hf where "hf = (\<lambda>x. (if x \<in> I then \<one> else undefined))(j := inv h)"
      with j ih have "hf \<in> Pi\<^sub>E I S"
        using subgroup.one_closed[OF i(3)] by force
      moreover have "finprod G hf I = inv h"
      proof -
        have "finprod G hf I = hf j \<otimes> finprod G hf (I - {j})"
          by (intro finprod_minus, use assms hf_def subgroup.subset[OF i(3)[OF j(1)]] j in auto)
        moreover have "hf j = inv h" using hf_def by simp
        moreover have "finprod G hf (I - {j}) = \<one>" by (rule finprod_one_eqI; use hf_def in simp)
        ultimately show ?thesis using subgroup.subset[OF i(3)[OF j(1)]] j(2) by auto
      qed
      ultimately show ?case unfolding image_def by (auto; metis)
    next
      case e: (eng a b)
      from e obtain f where f: "f \<in> Pi\<^sub>E I S" "a = finprod G f I" by blast
      from e obtain g where g: "g \<in> Pi\<^sub>E I S" "b = finprod G g I" by blast
      from f g have "a \<otimes> b = finprod G f I \<otimes> finprod G g I" by blast
      also have "\<dots> = finprod G (\<lambda>a. f a \<otimes> g a) I"
      proof(intro finprod_multf[symmetric])
        have "\<Union>(S ` I) \<subseteq> carrier G" using subgroup.subset[OF e(6)] by blast
        thus "f \<in> I \<rightarrow> carrier G" "g \<in> I \<rightarrow> carrier G"
          using f(1) g(1) unfolding PiE_def Pi_def by auto
      qed
      also have "\<dots> = finprod G (restrict (\<lambda>a. f a \<otimes> g a) I) I"
      proof(intro finprod_cong)
        show "I = I" by simp
        show "\<And>i. i \<in> I =simp=> f i \<otimes> g i = (\<lambda>a\<in>I. f a \<otimes> g a) i" by simp
        have fp: "f i \<in> (S i)" if "i \<in> I" for i using f that by auto
        have gp: "g i \<in> (S i)" if "i \<in> I" for i using g that by auto
        have "f i \<otimes> g i \<in> (S i)" if "i \<in> I" for i
          using subgroup.m_closed[OF e(6)[OF that] fp[OF that] gp[OF that]] .
        thus "((\<lambda>a. f a \<otimes> g a) \<in> I \<rightarrow> carrier G) = True" using subgroup.subset[OF e(6)] by auto
      qed
      finally have "a \<otimes> b = finprod G (restrict (\<lambda>a. f a \<otimes> g a) I) I" .
      moreover have "(restrict (\<lambda>a. f a \<otimes> g a) I) \<in> Pi\<^sub>E I S"
      proof -
        have fp: "f i \<in> (S i)" if "i \<in> I" for i using f that by auto
        have gp: "g i \<in> (S i)" if "i \<in> I" for i using g that by auto
        have "f i \<otimes> g i \<in> (S i)" if "i \<in> I" for i
          using subgroup.m_closed[OF e(6)[OF that] fp[OF that] gp[OF that]] .
        thus ?thesis by auto
      qed
      ultimately show ?case using f g by blast
    qed
  qed
qed

lemma (in comm_group) IDirProds_eq_finprod_Pi:
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> subgroup (S i) G"
  shows "IDirProds G S I = (\<lambda>x. finprod G x I) ` (Pi I S)" (is "?DP = ?fp")
proof -
  have "(\<lambda>x. finprod G x I) ` (Pi I S) = (\<lambda>x. finprod G x I) ` (Pi\<^sub>E I S)"
  proof
    have "Pi\<^sub>E I S \<subseteq> Pi I S" by blast
    thus "(\<lambda>x. finprod G x I) ` Pi\<^sub>E I S \<subseteq> (\<lambda>x. finprod G x I) ` Pi I S" by blast
    show "(\<lambda>x. finprod G x I) ` Pi I S \<subseteq> (\<lambda>x. finprod G x I) ` Pi\<^sub>E I S"
    proof
      fix x
      assume x: "x \<in> (\<lambda>x. finprod G x I) ` Pi I S"
      then obtain f where f: "x = finprod G f I" "f \<in> Pi I S" by blast
      moreover have "finprod G f I = finprod G (restrict f I) I"
        by (intro finprod_cong; use f(2) subgroup.subset[OF assms(2)] in fastforce)
      moreover have "restrict f I \<in> Pi\<^sub>E I S" using f(2) by simp
      ultimately show "x \<in> (\<lambda>x. finprod G x I) ` Pi\<^sub>E I S" by blast
    qed
  qed
  with IDirProds_eq_finprod_PiE[OF assms] show ?thesis by auto
qed

text \<open>If we switch one element from a set of generators, the generated set stays the same if both
elements can be generated from the others together with the switched element respectively.\<close>

lemma (in comm_group) generate_one_switched_exp_eqI:
  assumes "A \<subseteq> carrier G" "a \<in> A" "B = (A - {a}) \<union> {b}"
  and "f \<in> A \<rightarrow> (UNIV::int set)" "g \<in> B \<rightarrow> (UNIV::int set)"
  and "a = finprod G (\<lambda>x. x [^] g x) B" "b = finprod G (\<lambda>x. x [^] f x) A"
  shows "generate G A = generate G B"
proof(intro generate_one_switched_eqI[OF assms(1, 2, 3)]; cases "finite A")
  case True
  hence fB: "finite B" using assms(3) by blast
  have cB: "B \<subseteq> carrier G"
  proof -
    have "b \<in> carrier G"
      by (subst assms(7), intro finprod_closed, use assms(1, 4) int_pow_closed in fast)
    thus ?thesis using assms(1, 3) by blast
  qed
  show "a \<in> generate G B"
  proof(subst generate_eq_finprod_Pi_image[OF fB cB], rule)
    show "a = finprod G (\<lambda>x. x [^] g x) B" by fact
    have "x [^] g x \<in> generate G {x}" if "x \<in> B" for x using generate_pow[of x] cB that by blast
    thus "(\<lambda>x. x [^] g x) \<in> (\<Pi> a\<in>B. generate G {a})" unfolding Pi_def by blast
  qed
  show "b \<in> generate G A"
  proof(subst generate_eq_finprod_Pi_image[OF True assms(1)], rule)
    show "b = finprod G (\<lambda>x. x [^] f x) A" by fact
    have "x [^] f x \<in> generate G {x}" if "x \<in> A" for x
      using generate_pow[of x] assms(1) that by blast
    thus "(\<lambda>x. x [^] f x) \<in> (\<Pi> a\<in>A. generate G {a})" unfolding Pi_def by blast
  qed
next
  case False
  hence b: "b = \<one>" using assms(7) unfolding finprod_def by simp
  from False assms(3) have "infinite B" by simp
  hence a: "a = \<one>" using assms(6) unfolding finprod_def by simp
  show "a \<in> generate G B" using generate.one a by blast
  show "b \<in> generate G A" using generate.one b by blast
qed

text \<open>We can characterize a complementary family of subgroups when the only way to form the neutral
element as a product of picked elements from each subgroup is to pick the neutral element from each
subgroup.\<close>

lemma (in comm_group) compl_fam_imp_triv_finprod:
  assumes "compl_fam S I" "finite I" "\<And>i. i \<in> I \<Longrightarrow> subgroup (S i) G"
  and "finprod G f I = \<one>" "f \<in> Pi I S"
  shows "\<forall>i\<in>I. f i = \<one>"
proof (rule ccontr; clarify)
  from assms(5) have f: "f i \<in> (S i)" if "i \<in> I" for i using that by fastforce
  fix i
  assume i: "i \<in> I"
  have si: "subgroup (S i) G" using assms(3)[OF i] .
  consider (triv) "(S i) = {\<one>}" | (not_triv) "(S i) \<noteq> {\<one>}" by blast
  thus "f i = \<one>"
  proof (cases)
    case triv
    then show ?thesis using f[OF i] by blast
  next
    case not_triv
    show ?thesis
    proof (rule ccontr)
      have fc: "f i \<in> carrier G" using f[OF i] subgroup.subset[OF si] by blast
      assume no: "f i \<noteq> \<one>"
      have fH: "f i \<in> (S i)" using f[OF i] .
      from subgroup.m_inv_closed[OF si this] have ifi: "inv (f i) \<in> (S i)" .
      moreover have "inv (f i) \<noteq> \<one>" using no fc by simp
      moreover have "inv (f i) = finprod G f (I - {i})"
      proof -
        have "\<one> = finprod G f I" using assms(4) by simp
        also have "\<dots> = finprod G f (insert i (I - {i}))"
        proof -
          have "I = insert i (I - {i})" using i by fast
          thus ?thesis by simp
        qed
        also have "\<dots> = f i \<otimes> finprod G f (I - {i})"
        proof(intro finprod_insert)
          show "finite (I - {i})" using assms(2) by blast
          show "i \<notin> I - {i}" by blast
          show "f \<in> I - {i} \<rightarrow> carrier G" using assms(3) f subgroup.subset by blast
          show "f i \<in> carrier G" by fact
        qed
        finally have o: "\<one> = f i \<otimes> finprod G f (I - {i})" .
        show ?thesis
        proof(intro inv_equality)
          show "f i \<in> carrier G" by fact
          show "finprod G f (I - {i}) \<in> carrier G"
            by (intro finprod_closed; use assms(3) f subgroup.subset in blast)
          from m_comm[OF this fc] o show "finprod G f (I - {i}) \<otimes> f i = \<one>" by simp
        qed
      qed
      moreover have "finprod G f (I - {i}) \<in> IDirProds G S (I - {i})"
      proof (intro finprod_closed_subgroup IDirProds_is_subgroup)
        show "\<Union> (S ` (I - {i})) \<subseteq> carrier G" using assms(3) subgroup.subset by auto
        have "f j \<in> (IDirProds G S (I - {i}))" if "j \<in> (I - {i})" for j
          using IDirProds_incl[OF that] f that by blast
        thus "f \<in> I - {i} \<rightarrow> IDirProds G S (I - {i})" by blast
      qed
      ultimately have "\<not>complementary (S i) (IDirProds G S (I - {i}))"
        unfolding complementary_def by auto
      thus False using assms(1) i unfolding compl_fam_def by blast
    qed
  qed
qed

lemma (in comm_group) triv_finprod_imp_compl_fam:
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> subgroup (S i) G"
  and "\<forall>f \<in> Pi I S. finprod G f I = \<one> \<longrightarrow> (\<forall>i\<in>I. f i = \<one>)"
  shows "compl_fam S I"
proof (unfold compl_fam_def; rule)
  fix k
  assume k: "k \<in> I"
  let ?DP = "IDirProds G S (I - {k})"
  show "complementary (S k) ?DP"
  proof (rule ccontr; unfold complementary_def)
    have sk: "subgroup (S k) G" using assms(2)[OF k] .
    have sDP: "subgroup ?DP G"
      by (intro IDirProds_is_subgroup; use subgroup.subset[OF assms(2)] in blast)
    assume a: "(S k) \<inter> IDirProds G S (I - {k}) \<noteq> {\<one>}"
    then obtain x where x: "x \<in> (S k)" "x \<in> IDirProds G S (I - {k})" "x \<noteq> \<one>"
      using subgroup.one_closed sk sDP by blast
    then have "x \<in> (\<lambda>x. finprod G x (I - {k})) ` (Pi (I - {k}) S)"
      using IDirProds_eq_finprod_Pi[of "(I - {k})"] assms(1, 2) by blast
    then obtain ht where ht: "finprod G ht (I - {k}) = x" "ht \<in> Pi (I - {k}) S" by blast
    define h where h: "h = (ht(k := inv x))"
    then have hPi: "h \<in> Pi I S" using ht subgroup.m_inv_closed[OF assms(2)[OF k] x(1)] by auto
    have "finprod G h (I - {k}) = x"
    proof (subst ht(1)[symmetric], intro finprod_cong)
      show "I - {k} = I - {k}" by simp
      show "(h \<in> I - {k} \<rightarrow> carrier G) = True" using h ht(2) subgroup.subset[OF assms(2)]
        unfolding Pi_def id_def by auto
      show "\<And>i. i \<in> I - {k} =simp=> h i = ht i" using ht(2) h by simp
    qed
    moreover have "finprod G h I = h k \<otimes> finprod G h (I - {k})"
      by (intro finprod_minus; use k assms hPi subgroup.subset[OF assms(2)] Pi_def in blast)
    ultimately have "finprod G h I = inv x \<otimes> x" using h by simp
    then have "finprod G h I = \<one>" using subgroup.subset[OF sk] x(1) by auto
    moreover have "h k \<noteq> \<one>" using h x(3) subgroup.subset[OF sk] x(1) by force
    ultimately show False using assms(3) k hPi by blast
  qed
qed

lemma (in comm_group) triv_finprod_iff_compl_fam_Pi:
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> subgroup (S i) G"
  shows "compl_fam S I \<longleftrightarrow> (\<forall>f \<in> Pi I S. finprod G f I = \<one> \<longrightarrow> (\<forall>i\<in>I. f i = \<one>))"
  using compl_fam_imp_triv_finprod triv_finprod_imp_compl_fam assms by blast

lemma (in comm_group) triv_finprod_iff_compl_fam_PiE:
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> subgroup (S i) G"
  shows "compl_fam S I \<longleftrightarrow> (\<forall>f \<in> Pi\<^sub>E I S. finprod G f I = \<one> \<longrightarrow> (\<forall>i\<in>I. f i = \<one>))"
proof
  show "compl_fam S I \<Longrightarrow> \<forall>f\<in>Pi\<^sub>E I S. finprod G f I = \<one> \<longrightarrow> (\<forall>i\<in>I. f i = \<one>)"
    using triv_finprod_iff_compl_fam_Pi[OF assms] by auto
  have "\<forall>f\<in>Pi\<^sub>E I S. finprod G f I = \<one> \<longrightarrow> (\<forall>i\<in>I. f i = \<one>)
    \<Longrightarrow> \<forall>f\<in>Pi I S. finprod G f I = \<one> \<longrightarrow> (\<forall>i\<in>I. f i = \<one>)"
  proof(rule+)
    fix f i
    assume f: "f \<in> Pi I S" "finprod G f I = \<one>" and i: "i \<in> I"
    assume allf: "\<forall>f\<in>Pi\<^sub>E I S. finprod G f I = \<one> \<longrightarrow> (\<forall>i\<in>I. f i = \<one>)"
    have "f i = restrict f I i" using i by simp
    moreover have "finprod G (restrict f I) I = finprod G f I"
      using f subgroup.subset[OF assms(2)] unfolding Pi_def by (intro finprod_cong; auto)
    moreover have "restrict f I \<in> Pi\<^sub>E I S" using f by simp
    ultimately show "f i = \<one>" using allf f i by metis
  qed
  thus "\<forall>f\<in>Pi\<^sub>E I S. finprod G f I = \<one> \<longrightarrow> (\<forall>i\<in>I. f i = \<one>) \<Longrightarrow> compl_fam S I"
    using triv_finprod_iff_compl_fam_Pi[OF assms] by presburger
qed

text \<open>The finite product also distributes when nested.\<close>

(* Manuel Eberl, TODO: move to library *)
lemma (in comm_monoid) finprod_Sigma:
  assumes "finite A" "\<And>x. x \<in> A \<Longrightarrow> finite (B x)"
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> B x \<Longrightarrow> g x y \<in> carrier G"
  shows   "(\<Otimes>x\<in>A. \<Otimes>y\<in>B x. g x y) = (\<Otimes>z\<in>Sigma A B. case z of (x, y) \<Rightarrow> g x y)"
  using assms
proof (induction A rule: finite_induct)
  case (insert x A)
  have "(\<Otimes>z\<in>Sigma (insert x A) B. case z of (x, y) \<Rightarrow> g x y) =
          (\<Otimes>z\<in>Pair x ` B x. case z of (x, y) \<Rightarrow> g x y) \<otimes> (\<Otimes>z\<in>Sigma A B. case z of (x, y) \<Rightarrow> g x y)"
    unfolding Sigma_insert using insert.prems insert.hyps
    by (subst finprod_Un_disjoint) auto
  also have "(\<Otimes>z\<in>Sigma A B. case z of (x, y) \<Rightarrow> g x y) = (\<Otimes>x\<in>A. \<Otimes>y\<in>B x. g x y)"
    using insert.prems insert.hyps by (subst insert.IH [symmetric]) auto
  also have "(\<Otimes>z\<in>Pair x ` B x. case z of (x, y) \<Rightarrow> g x y) = (\<Otimes>y\<in>B x. g x y)"
    using insert.prems insert.hyps by (subst finprod_reindex) (auto intro: inj_onI)
  finally show ?case
    using insert.hyps insert.prems by simp
qed auto

text \<open>With the now proven facts, we are able to provide criterias to inductively construct a
group that is the internal direct product of a set of generators.\<close>

(* belongs to IDirProd, but uses finprod stuff *)
lemma (in comm_group) idirprod_generate_ind:
  assumes "finite gs" "gs \<subseteq> carrier G" "g \<in> carrier G"
          "is_idirprod (generate G gs) (\<lambda>g. generate G {g}) gs"
          "complementary (generate G {g}) (generate G gs)"
  shows "is_idirprod (generate G (gs \<union> {g})) (\<lambda>g. generate G {g}) (gs \<union> {g})"
proof(cases "g \<in> gs")
  case True
  hence "gs = (gs \<union> {g})" by blast
  thus ?thesis using assms(4) by auto 
next
  case gngs: False
  show ?thesis
  proof (intro is_idirprod_subgroup_suffices)
    have gsgc: "gs \<union> {g} \<subseteq> carrier G" using assms(2, 3) by blast
    thus "generate G (gs \<union> {g}) = IDirProds G (\<lambda>g. generate G {g}) (gs \<union> {g})"
      unfolding IDirProds_def using generate_idem_Un by presburger
    show "\<forall>i\<in>gs \<union> {g}. subgroup (generate G {i}) G" using generate_is_subgroup gsgc by auto
    have sg: "subgroup (generate G {g}) G" by (intro generate_is_subgroup, use assms(3) in blast)
    from assms(4) is_idirprod_def have ih: "\<forall>x. x \<in> gs \<longrightarrow> generate G {x} \<lhd> G"
                                           "compl_fam (\<lambda>g. generate G {g}) gs"
      by fastforce+
    hence ca: "complementary (generate G {a}) (generate G (gs - {a}))" if "a \<in> gs" for a
      unfolding compl_fam_def IDirProds_def
      using gsgc generate_idem_Un[of "gs - {a}"] that by fastforce
    have aux: "gs \<union> {g} - {i} \<subseteq> carrier G" for i using gsgc by blast
    show "compl_fam (\<lambda>g. generate G {g}) (gs \<union> {g})"
    proof(unfold compl_fam_def IDirProds_def, subst generate_idem_Un[OF aux],
          rule, rule ccontr)
      fix h
      assume h: "h \<in> gs \<union> {g}"
      assume c: "\<not> complementary (generate G {h}) (generate G (gs \<union> {g} - {h}))"
      show "False"
      proof (cases "h = g")
        case True
        with c have "\<not> complementary (generate G {g}) (generate G (gs - {g}))" by auto
        moreover have "complementary (generate G {g}) (generate G (gs - {g}))"
          by (rule subgroup_subset_complementary[OF generate_is_subgroup generate_is_subgroup[of gs]
                   generate_is_subgroup mono_generate], use assms(2, 3, 5) in auto)
        ultimately show False by blast
      next
        case hng: False
        hence h: "h \<in> gs" "h \<noteq> g" using h by blast+
        hence "gs \<union> {g} - {h} = gs - {h} \<union> {g}" by blast
        with c have c: "\<not> complementary (generate G {h}) (generate G (gs - {h} \<union> {g}))" by argo
        then obtain k where k: "k \<in> generate G {h}" "k \<in> generate G (gs - {h} \<union> {g})" "k \<noteq> \<one>"
          unfolding complementary_def using generate.one by blast 
        with ca have kngh: "k \<notin> generate G (gs - {h})" using h unfolding complementary_def by blast
        from k(2) generate_eq_finprod_PiE_image[of "gs - {h} \<union> {g}"] assms(1) gsgc
        obtain f where f:
          "k = finprod G f (gs - {h} \<union> {g})" "f \<in> (\<Pi>\<^sub>E a\<in>gs - {h} \<union> {g}. generate G {a})"
          by blast
        have fg: "f a \<in> generate G {a}" if "a \<in> (gs - {h} \<union> {g})" for a using that f(2) by blast
        have fc: "f a \<in> carrier G" if "a \<in> (gs - {h} \<union> {g})" for a
        proof -
          have "generate G {a} \<subseteq> carrier G" if "a \<in> (gs - {h} \<union> {g})" for a
            using that generate_incl[of "{a}"] gsgc by blast
          thus "f a \<in> carrier G" using that fg by auto
        qed
        have kp: "k = f g \<otimes> finprod G f (gs - {h})"
        proof -
          have "(gs - {h} \<union> {g}) = insert g (gs - {h})" by fast
          moreover have "finprod G f (insert g (gs - {h})) = f g \<otimes> finprod G f (gs - {h})"
            by (intro finprod_insert, use fc assms(1) gngs in auto)
          ultimately show ?thesis using f(1) by argo
        qed
        have fgsh: "finprod G f (gs - {h}) \<in> generate G (gs - {h})"
        proof(intro finprod_closed_subgroup[OF generate_is_subgroup])
          show "gs - {h} \<subseteq> carrier G" using gsgc by blast
          have "f a \<in> generate G (gs - {h})" if "a \<in> (gs - {h})" for a
            using mono_generate[of "{a}" "gs - {h}"] fg that by blast
          thus "f \<in> gs - {h} \<rightarrow> generate G (gs - {h})" by blast
        qed
        have "f g \<otimes> finprod G f (gs - {h}) \<notin> generate G gs"
        proof
          assume fpgs: "f g \<otimes> finprod G f (gs - {h}) \<in> generate G gs"
          from fgsh have fgsgs: "finprod G f (gs - {h}) \<in> generate G gs"
            using mono_generate[of "gs - {h}" gs] by blast
          have fPi: "f \<in> (\<Pi> a\<in>(gs - {h}). generate G {a})" using f by blast
          have gI: "generate G (gs - {h})
                  = (\<lambda>x. finprod G x (gs - {h})) ` (\<Pi> a\<in>gs - {h}. generate G {a})"
            using generate_eq_finprod_Pi_image[of "gs - {h}"] assms(1, 2) by blast
          have fgno: "f g \<noteq> \<one>"
          proof (rule ccontr)
            assume o: "\<not> f g \<noteq> \<one>"
            hence kf: "k = finprod G f (gs - {h})" using kp finprod_closed fc by auto
            hence "k \<in> generate G (gs - {h})" using fPi gI by blast
            thus False using k ca h unfolding complementary_def by blast
          qed
          from fpgs have "f g \<in> generate G gs"
            using subgroup.mult_in_cancel_right[OF generate_is_subgroup[OF assms(2)] fc[of g] fgsgs]
            by blast
          with fgno assms(5) fg[of g] show "False" unfolding complementary_def by blast
        qed
        moreover have "k \<in> generate G gs" using k(1) mono_generate[of "{h}" gs] h(1) by blast
        ultimately show False using kp by blast
      qed
    qed
  qed
qed

end