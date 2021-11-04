section\<open>The Delta System Lemma\label{sec:dsl}\<close>

theory Delta_System
  imports 
    Cardinal_Library

begin

text\<open>A \<^emph>\<open>delta system\<close> is family of sets with a common pairwise
intersection.\<close>

definition
  delta_system :: "i \<Rightarrow> o" where
  "delta_system(D) \<equiv> \<exists>r. \<forall>A\<in>D. \<forall>B\<in>D. A \<noteq> B \<longrightarrow> A \<inter> B = r"

lemma delta_systemI[intro]: 
  assumes "\<forall>A\<in>D. \<forall>B\<in>D. A \<noteq> B \<longrightarrow> A \<inter> B = r"
  shows "delta_system(D)"
  using assms unfolding delta_system_def by simp

lemma delta_systemD[dest]:
  "delta_system(D) \<Longrightarrow> \<exists>r. \<forall>A\<in>D. \<forall>B\<in>D. A \<noteq> B \<longrightarrow> A \<inter> B = r"
  unfolding delta_system_def by simp

text\<open>Hence, pairwise intersections equal the intersection of the whole
family.\<close>

lemma delta_system_root_eq_Inter:
  assumes "delta_system(D)"
  shows "\<forall>A\<in>D. \<forall>B\<in>D. A \<noteq> B \<longrightarrow> A \<inter> B = \<Inter>D"
proof (clarify, intro equalityI, auto)
  fix A' B' x C
  assume hyp:"A'\<in>D" "B'\<in> D" "A'\<noteq>B'" "x\<in>A'" "x\<in>B'" "C\<in>D"
  with assms
  obtain r where delta:"\<forall>A\<in>D. \<forall>B\<in>D. A \<noteq> B \<longrightarrow> A \<inter> B = r"
    by auto
  show "x \<in> C"
  proof (cases "C=A'")
    case True
    with hyp and assms
    show ?thesis by simp
  next
    case False
    moreover
    note hyp
    moreover from calculation and delta
    have "r = C \<inter> A'" "A' \<inter> B' = r" "x\<in>r" by auto
    ultimately
    show ?thesis by simp
  qed
qed

text\<open>The \<^emph>\<open>Delta System Lemma\<close> (DSL) states that any uncountable family of
finite sets includes an uncountable delta system. This is the simplest
non trivial version; others, for cardinals greater than \<^term>\<open>\<aleph>\<^bsub>1\<^esub>\<close>  assume
some weak versions of the generalized continuum hypothesis for the
cardinals involved.

The proof is essentially the one in \cite[III.2.6]{kunen2011set} for the
case  \<^term>\<open>\<aleph>\<^bsub>1\<^esub>\<close>; another similar presentation can be found in
\cite[Chap.~16]{JW}.\<close>

lemma delta_system_Aleph1:
  assumes "\<forall>A\<in>F. Finite(A)" "F \<approx> \<aleph>\<^bsub>1\<^esub>"
  shows "\<exists>D. D \<subseteq> F \<and> delta_system(D) \<and> D \<approx> \<aleph>\<^bsub>1\<^esub>"
proof -
  text\<open>Since all members are finite,\<close>
  from \<open>\<forall>A\<in>F. Finite(A)\<close>
  have "(\<lambda>A\<in>F. |A|) : F \<rightarrow> \<omega>" (is "?cards : _")
    by (rule_tac lam_type) simp
  moreover from this
  have a:"?cards -`` {n} = { A\<in>F . |A| = n }" for n
    using vimage_lam by auto
  moreover
  note \<open>F \<approx> \<aleph>\<^bsub>1\<^esub>\<close>
  moreover from calculation
  text\<open>there are uncountably many have the same cardinal:\<close>
  obtain n where "n\<in>\<omega>" "|?cards -`` {n}| = \<aleph>\<^bsub>1\<^esub>"
    using eqpoll_Aleph1_cardinal_vimage[of F ?cards] by auto
  moreover
  define G where "G \<equiv> ?cards -`` {n}"
  moreover from calculation
  have "G \<subseteq> F" by auto
  ultimately
  text\<open>Therefore, without loss of generality, we can assume that all
  elements of the family have cardinality \<^term>\<open>n\<in>\<omega>\<close>.\<close>
  have "A\<in>G \<Longrightarrow> |A| = n" and "G \<approx> \<aleph>\<^bsub>1\<^esub>" for A
    using cardinal_Card_eqpoll_iff by auto
  with \<open>n\<in>\<omega>\<close>
  text\<open>So we prove the result by induction on this \<^term>\<open>n\<close> and
  generalizing \<^term>\<open>G\<close>, since the argument requires changing the
  family in order to apply the inductive hypothesis.\<close>
  have "\<exists>D. D \<subseteq> G \<and> delta_system(D) \<and> D \<approx> \<aleph>\<^bsub>1\<^esub>"
  proof (induct arbitrary:G)
    case 0 \<comment> \<open>This case is impossible\<close>
    then
    have "G \<subseteq> {0}"
      using cardinal_0_iff_0 by auto
    with \<open>G \<approx> \<aleph>\<^bsub>1\<^esub>\<close>
    show ?case
      using nat_lt_Aleph1 subset_imp_le_cardinal[of G "{0}"]
        lt_trans2 cardinal_Card_eqpoll_iff by auto
  next
    case (succ n)
    then
    have "\<forall>a\<in>G. Finite(a)"
      using Finite_cardinal_iff' nat_into_Finite[of "succ(n)"]
      by fastforce
    show "\<exists>D. D \<subseteq> G \<and> delta_system(D) \<and> D \<approx> \<aleph>\<^bsub>1\<^esub>"
    proof (cases "\<exists>p. {A\<in>G . p \<in> A} \<approx> \<aleph>\<^bsub>1\<^esub>")
      case True \<comment> \<open>the positive case, uncountably many sets with a
                    common element\<close>
      then
      obtain p where "{A\<in>G . p \<in> A} \<approx> \<aleph>\<^bsub>1\<^esub>" by blast
      moreover from this
      have "{A-{p} . A\<in>{X\<in>G. p\<in>X}} \<approx> \<aleph>\<^bsub>1\<^esub>" (is "?F \<approx> _")
        using Diff_bij[of "{A\<in>G . p \<in> A}" "{p}"]
          comp_bij[OF bij_converse_bij, where C="\<aleph>\<^bsub>1\<^esub>"] by fast
      text\<open>Now using the hypothesis of the successor case,\<close>
      moreover from \<open>\<And>A. A\<in>G \<Longrightarrow> |A|=succ(n)\<close> \<open>\<forall>a\<in>G. Finite(a)\<close>
        and this
      have "p\<in>A \<Longrightarrow> A\<in>G \<Longrightarrow> |A - {p}| = n" for A
        using Finite_imp_succ_cardinal_Diff[of _ p] by force
      moreover from this and \<open>n\<in>\<omega>\<close>
      have "\<forall>a\<in>?F. Finite(a)"
        using Finite_cardinal_iff' nat_into_Finite by auto
      moreover
      text\<open>we may apply the inductive hypothesis to the new family \<^term>\<open>?F\<close>:\<close>
      note \<open>(\<And>A. A \<in> ?F \<Longrightarrow> |A| = n) \<Longrightarrow> ?F \<approx> \<aleph>\<^bsub>1\<^esub> \<Longrightarrow>
             \<exists>D. D \<subseteq> ?F \<and> delta_system(D) \<and> D \<approx> \<aleph>\<^bsub>1\<^esub>\<close>
      ultimately
      obtain D where "D\<subseteq>{A-{p} . A\<in>{X\<in>G. p\<in>X}}" "delta_system(D)" "D \<approx> \<aleph>\<^bsub>1\<^esub>"
        by auto
      moreover from this
      obtain r where "\<forall>A\<in>D. \<forall>B\<in>D. A \<noteq> B \<longrightarrow> A \<inter> B = r"
        by fastforce
      then
      have "\<forall>A\<in>D.\<forall>B\<in>D. A\<union>{p} \<noteq> B\<union>{p}\<longrightarrow>(A \<union> {p}) \<inter> (B \<union> {p}) = r\<union>{p}"
        by blast
      ultimately
      have "delta_system({B \<union> {p} . B\<in>D})" (is "delta_system(?D)")
        by fastforce
      moreover from \<open>D \<approx> \<aleph>\<^bsub>1\<^esub>\<close>
      have "|D| = \<aleph>\<^bsub>1\<^esub>" "Infinite(D)"
        using cardinal_eqpoll_iff
        by (auto intro!: uncountable_iff_subset_eqpoll_Aleph1[THEN iffD2]
            uncountable_imp_Infinite) force
      moreover from this
      have "?D \<approx> \<aleph>\<^bsub>1\<^esub>"
        using cardinal_map_Un[of D "{p}"] naturals_lt_nat
          cardinal_eqpoll_iff[THEN iffD1] by simp
      moreover
      note \<open>D \<subseteq> {A-{p} . A\<in>{X\<in>G. p\<in>X}}\<close>
      have "?D \<subseteq> G"
      proof -
        {
          fix A
          assume "A\<in>G" "p\<in>A"
          moreover from this
          have "A = A - {p} \<union> {p}"
            by blast
          ultimately
          have "A -{p} \<union> {p} \<in> G"
            by auto
        }
        with \<open>D \<subseteq> {A-{p} . A\<in>{X\<in>G. p\<in>X}}\<close>
        show ?thesis
          by blast
      qed
      ultimately
      show "\<exists>D. D \<subseteq> G \<and> delta_system(D) \<and> D \<approx> \<aleph>\<^bsub>1\<^esub>" by auto
    next
      case False
      note \<open>\<not> (\<exists>p. {A \<in> G . p \<in> A} \<approx> \<aleph>\<^bsub>1\<^esub>)\<close> \<comment> \<open>the other case\<close>
      moreover from \<open>G \<approx> \<aleph>\<^bsub>1\<^esub>\<close>
      have "{A \<in> G . p \<in> A} \<lesssim> \<aleph>\<^bsub>1\<^esub>" (is "?G(p) \<lesssim> _") for p
        by (blast intro:lepoll_eq_trans[OF subset_imp_lepoll])
      ultimately
      have "?G(p) \<prec> \<aleph>\<^bsub>1\<^esub>" for p
        unfolding lesspoll_def by simp
      then (* may omit the previous step if unfolding here: *)
      have "?G(p) \<lesssim> \<omega>" for p
        using lesspoll_aleph_plus_one[of 0] Aleph_zero_eq_nat by auto
      moreover
      have "{A \<in> G . S \<inter> A \<noteq> 0} = (\<Union>p\<in>S. ?G(p))" for S
        by auto
      ultimately
      have "countable(S) \<Longrightarrow> countable({A \<in> G . S \<inter> A \<noteq> 0})" for S
        using InfCard_nat Card_nat
         le_Card_iff[THEN iffD2, THEN [3] leqpoll_imp_cardinal_UN_le,
           THEN [2] le_Card_iff[THEN iffD1], of \<omega> S]
        unfolding countable_def by simp
      text\<open>For every countable subfamily of \<^term>\<open>G\<close> there is another some
      element disjoint from all of them:\<close>
      have "\<exists>A\<in>G. \<forall>S\<in>X. S \<inter> A = 0" if "|X| < \<aleph>\<^bsub>1\<^esub>" "X \<subseteq> G" for X
      proof -
        from \<open>n\<in>\<omega>\<close> \<open>\<And>A. A\<in>G \<Longrightarrow> |A| = succ(n)\<close>
        have "A\<in>G \<Longrightarrow> Finite(A)" for A
          using cardinal_Card_eqpoll_iff
          unfolding Finite_def by fastforce
        with \<open>X\<subseteq>G\<close>
        have "A\<in>X \<Longrightarrow> countable(A)" for A
          using Finite_imp_countable by auto
        with \<open>|X| < \<aleph>\<^bsub>1\<^esub>\<close>
        have "countable(\<Union>X)"
          using Card_nat[THEN cardinal_lt_csucc_iff, of X]
            countable_union_countable countable_iff_cardinal_le_nat
          unfolding Aleph_def by simp
        with \<open>countable(_) \<Longrightarrow> countable({A \<in> G . _  \<inter> A \<noteq> 0})\<close>
        have "countable({A \<in> G . (\<Union>X) \<inter> A \<noteq> 0})" .
        with \<open>G \<approx> \<aleph>\<^bsub>1\<^esub>\<close>
        obtain B where "B\<in>G" "B \<notin> {A \<in> G . (\<Union>X) \<inter> A \<noteq> 0}" 
          using nat_lt_Aleph1 cardinal_Card_eqpoll_iff[of "\<aleph>\<^bsub>1\<^esub>" G]
            uncountable_not_subset_countable[of "{A \<in> G . (\<Union>X) \<inter> A \<noteq> 0}" G]
            uncountable_iff_nat_lt_cardinal
          by auto
        then
        show "\<exists>A\<in>G. \<forall>S\<in>X. S \<inter> A = 0" by auto
      qed
      moreover from \<open>G \<approx> \<aleph>\<^bsub>1\<^esub>\<close>
      obtain b where "b\<in>G"
        using uncountable_iff_subset_eqpoll_Aleph1
          uncountable_not_empty by blast
      ultimately
      text\<open>Hence, the hypotheses to perform a bounded-cardinal selection
      are satisfied,\<close>
      obtain S where "S:\<aleph>\<^bsub>1\<^esub>\<rightarrow>G" "\<alpha>\<in>\<aleph>\<^bsub>1\<^esub> \<Longrightarrow> \<beta>\<in>\<aleph>\<^bsub>1\<^esub> \<Longrightarrow> \<alpha><\<beta> \<Longrightarrow> S`\<alpha> \<inter> S`\<beta> = 0"
        for \<alpha> \<beta>
        using bounded_cardinal_selection[of "\<aleph>\<^bsub>1\<^esub>" G "\<lambda>s a. s \<inter> a = 0" b]
        by force
      then
      have "\<alpha> \<in> \<aleph>\<^bsub>1\<^esub> \<Longrightarrow> \<beta> \<in> \<aleph>\<^bsub>1\<^esub> \<Longrightarrow> \<alpha>\<noteq>\<beta> \<Longrightarrow> S`\<alpha> \<inter> S`\<beta> = 0" for \<alpha> \<beta>
        using lt_neq_symmetry[of "\<aleph>\<^bsub>1\<^esub>" "\<lambda>\<alpha> \<beta>. S`\<alpha> \<inter> S`\<beta> = 0"] Card_is_Ord
        by auto blast
      text\<open>and a symmetry argument shows that obtained \<^term>\<open>S\<close> is
      an injective  \<^term>\<open>\<aleph>\<^bsub>1\<^esub>\<close>-sequence of disjoint elements of \<^term>\<open>G\<close>.\<close>
      moreover from this and \<open>\<And>A. A\<in>G \<Longrightarrow> |A| = succ(n)\<close> \<open>S : \<aleph>\<^bsub>1\<^esub> \<rightarrow> G\<close>
      have "S \<in> inj(\<aleph>\<^bsub>1\<^esub>, G)"
        using cardinal_succ_not_0 Int_eq_zero_imp_not_eq[of "\<aleph>\<^bsub>1\<^esub>" "\<lambda>x. S`x"]
        unfolding inj_def by fastforce
      moreover from calculation
      have "range(S) \<approx> \<aleph>\<^bsub>1\<^esub>"
        using inj_bij_range eqpoll_sym unfolding eqpoll_def by fast
      moreover from calculation
      have "range(S) \<subseteq> G"
        using inj_is_fun range_fun_subset_codomain by fast
      ultimately
      show "\<exists>D. D \<subseteq> G \<and> delta_system(D) \<and> D \<approx> \<aleph>\<^bsub>1\<^esub>"
        using inj_is_fun range_eq_image[of S "\<aleph>\<^bsub>1\<^esub>" G]
          image_function[OF fun_is_function, OF inj_is_fun, of S "\<aleph>\<^bsub>1\<^esub>" G]
          domain_of_fun[OF inj_is_fun, of S "\<aleph>\<^bsub>1\<^esub>" G]
        by (rule_tac x="S``\<aleph>\<^bsub>1\<^esub>" in exI) auto
      text\<open>This finishes the successor case and hence the proof.\<close>
    qed
  qed
  with \<open>G \<subseteq> F\<close>
  show ?thesis by blast
qed

lemma delta_system_uncountable:
  assumes "\<forall>A\<in>F. Finite(A)" "uncountable(F)"
  shows "\<exists>D. D \<subseteq> F \<and> delta_system(D) \<and> D \<approx> \<aleph>\<^bsub>1\<^esub>"
proof -
  from assms
  obtain S where "S \<subseteq> F" "S \<approx> \<aleph>\<^bsub>1\<^esub>"
    using uncountable_iff_subset_eqpoll_Aleph1[of F] by auto
  moreover from \<open>\<forall>A\<in>F. Finite(A)\<close> and this
  have "\<forall>A\<in>S. Finite(A)" by auto
  ultimately
  show ?thesis using delta_system_Aleph1[of S]
    by auto
qed

end