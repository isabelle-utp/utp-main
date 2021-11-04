(*
    File:     Generated_Groups_Extend.thy
    Author:   Joseph Thommes, TU München
*)
section \<open>Generated Groups\<close>

theory Generated_Groups_Extend
  imports Miscellaneous_Groups "HOL-Algebra.Algebra"
begin

text \<open>This section extends the lemmas and facts about \<open>generate\<close>. Starting with a basic fact.\<close>

lemma (in group) generate_sincl:
  "A \<subseteq> generate G A"
  using generate.incl by fast

text \<open>The following lemmas reflect some of the idempotence characteristics of \<open>generate\<close> and have
proved useful at several occasions.\<close>

lemma (in group) generate_idem:
  assumes "A \<subseteq> carrier G"
  shows "generate G (generate G A) = generate G A"
  using assms generateI group.generate_is_subgroup by blast

lemma (in group) generate_idem':
  assumes "A \<subseteq> carrier G" "B \<subseteq> carrier G"
  shows "generate G (generate G A \<union> B) = generate G (A \<union> B)"
proof
  show "generate G (generate G A \<union> B) \<subseteq> generate G (A \<union> B)"
  proof -
    have "generate G A \<union> B \<subseteq> generate G (A \<union> B)"
    proof -
      have "generate G A \<subseteq> generate G (A \<union> B)" using mono_generate by simp
      moreover have "B \<subseteq> generate G (A \<union> B)" by (simp add: generate.incl subset_iff)
      ultimately show ?thesis by simp
    qed
    then have "generate G (generate G A \<union> B) \<subseteq> generate G (generate G (A \<union> B))"
      using mono_generate by auto
    with generate_idem[of "A \<union> B"] show ?thesis using assms by simp
  qed
  show "generate G (A \<union> B) \<subseteq> generate G (generate G A \<union> B)"
  proof -
    have "A \<subseteq> generate G A" using generate.incl by fast
    thus ?thesis using mono_generate[of "A \<union> B" "generate G A \<union> B"] by blast
  qed
qed

lemma (in group) generate_idem'_right:
  assumes "A \<subseteq> carrier G" "B \<subseteq> carrier G"
  shows "generate G (A \<union> generate G B) = generate G (A \<union> B)"
  using generate_idem'[OF assms(2) assms(1)] by (simp add: sup_commute)

lemma (in group) generate_idem_Un:
  assumes "A \<subseteq> carrier G"
  shows "generate G (\<Union>x\<in>A. generate G {x}) = generate G A"
proof
  have "A \<subseteq> (\<Union>x\<in>A. generate G {x})" using generate.incl by force
  thus "generate G A \<subseteq> generate G (\<Union>x\<in>A. generate G {x})" using mono_generate by presburger
  have "\<And>x. x \<in> A \<Longrightarrow> generate G {x} \<subseteq> generate G A" using mono_generate by auto
  hence "(\<Union>x\<in>A. generate G {x}) \<subseteq> generate G A" by blast
  thus "generate G (\<Union>x\<in>A. generate G {x}) \<subseteq> generate G A"
    using generate_idem[OF assms] mono_generate by blast
qed

lemma (in group) generate_idem_fUn:
  assumes "f A \<subseteq> carrier G"
  shows "generate G (\<Union> {generate G {x} |x. x \<in> f A}) = generate G (f A)"
proof
  have "f A \<subseteq> \<Union> {generate G {x} |x. x \<in> f A}"
  proof
    fix x
    assume x: "x \<in> f A"
    have "x \<in> generate G {x}" using generate.incl by fast
    thus "x \<in> \<Union> {generate G {x} |x. x \<in> f A}" using x by blast
  qed
  thus "generate G (f A) \<subseteq> generate G (\<Union> {generate G {x} |x. x \<in> f A})" using mono_generate by auto
  have "\<And>x. x \<in> f A \<Longrightarrow> generate G {x} \<subseteq> generate G (f A)" using mono_generate by simp
  hence "(\<Union> {generate G {x} |x. x \<in> f A}) \<subseteq> generate G (f A)" by blast
  with mono_generate[OF this] show "generate G (\<Union> {generate G {x} |x. x \<in> f A}) \<subseteq> generate G (f A)"
    using generate_idem[OF assms] by simp
qed

lemma (in group) generate_idem_fim_Un:
  assumes "\<Union>(f ` A) \<subseteq> carrier G"
  shows "generate G (\<Union>S \<in> A. generate G (f S)) = generate G (\<Union> {generate G {x} |x. x \<in> \<Union> (f ` A)})"
proof
  
  have "\<And>S. S \<in> A \<Longrightarrow> generate G (f S) = generate G (\<Union> {generate G {x} |x. x \<in> f S})"
    using generate_idem_fUn[of f] assms by blast
  then have "generate G (\<Union>S \<in> A. generate G (f S))
           = generate G (\<Union>S \<in> A. generate G (\<Union> {generate G {x} |x. x \<in> f S}))" by simp

  have "\<Union> {generate G {x} |x. x \<in> \<Union> (f ` A)} \<subseteq> (\<Union>S\<in>A. generate G (f S))"
  proof
    fix x
    assume x: "x \<in> \<Union> {generate G {x} |x. x \<in> \<Union> (f ` A)}"
    then obtain a where a: "x \<in> generate G {a}" "a \<in> \<Union> (f ` A)" by blast
    then obtain M where M: "a \<in> f M" "M \<in> A" by blast
    then have "generate G {a} \<subseteq> generate G (f M)"
      using generate.incl[OF M(1), of G] mono_generate[of "{a}" "generate G (f M)"]
            generate_idem assms by auto
    then have "x \<in> generate G (f M)" using a by blast
    thus "x \<in> (\<Union>S\<in>A. generate G (f S))" using M by blast
  qed
  thus "generate G (\<Union> {generate G {x} |x. x \<in> \<Union> (f ` A)}) \<subseteq> generate G (\<Union>S\<in>A. generate G (f S))"
    using mono_generate by simp
  have a: "generate G (\<Union>S\<in>A. generate G (f S)) \<subseteq> generate G (\<Union> (f ` A))"
  proof -
    have "\<And>S. S \<in> A \<Longrightarrow> generate G (f S) \<subseteq> generate G (\<Union> (f ` A))"
      using mono_generate[of _ "\<Union> (f ` A)"] by blast
    then have "(\<Union>S\<in>A. generate G (f S)) \<subseteq> generate G (\<Union> (f ` A))" by blast
    then have "generate G (\<Union>S\<in>A. generate G (f S)) \<subseteq> generate G (generate G (\<Union> (f ` A)))"
      using mono_generate by meson
    thus "generate G (\<Union>S\<in>A. generate G (f S)) \<subseteq>  generate G (\<Union> (f ` A))"
      using generate_idem assms by blast
  qed
  have "\<Union> {generate G {x} |x. x \<in> \<Union> (f ` A)} = (\<Union>x\<in>\<Union> (f ` A). generate G {x})" by blast
  with generate_idem_Un[OF assms]
  have "generate G (\<Union> {generate G {x} |x. x \<in> \<Union> (f ` A)}) = generate G (\<Union> (f ` A))" by simp
  with a show "generate G (\<Union>S\<in>A. generate G (f S))
             \<subseteq> generate G (\<Union> {generate G {x} |x. x \<in> \<Union> (f ` A)})" by blast
qed

text \<open>The following two rules allow for convenient proving of the equality of two generated sets.\<close>

lemma (in group) generate_eqI:
  assumes "A \<subseteq> carrier G" "B \<subseteq> carrier G" "A \<subseteq> generate G B" "B \<subseteq> generate G A"
  shows "generate G A = generate G B"
  using assms generate_idem by (metis generate_idem' inf_sup_aci(5) sup.absorb2)

lemma (in group) generate_one_switched_eqI:
  assumes "A \<subseteq> carrier G" "a \<in> A" "B = (A - {a}) \<union> {b}"
  and "b \<in> generate G A" "a \<in> generate G B"
  shows "generate G A = generate G B"
proof(intro generate_eqI)
  show "A \<subseteq> carrier G" by fact
  show "B \<subseteq> carrier G" using assms generate_incl by blast
  show "A \<subseteq> generate G B" using assms generate_sincl[of B] by blast
  show "B \<subseteq> generate G A" using assms generate_sincl[of A] by blast
qed

lemma (in group) generate_subset_eqI:
  assumes "A \<subseteq> carrier G" "B \<subseteq> A" "A - B \<subseteq> generate G B"
  shows "generate G A = generate G B"
proof
  show "generate G B \<subseteq> generate G A" by (intro mono_generate, fact)
  show "generate G A \<subseteq> generate G B"
  proof(subst generate_idem[of "B", symmetric])
    show "generate G A \<subseteq> generate G (generate G B)"
      by (intro mono_generate, use assms generate_sincl[of B] in auto)
  qed (use assms in blast)
qed

text \<open>Some smaller lemmas about \<open>generate\<close>.\<close>

lemma (in group) generate_subset_change_eqI:
  assumes "A \<subseteq> carrier G" "B \<subseteq> carrier G" "C \<subseteq> carrier G" "generate G A = generate G B"
  shows "generate G (A \<union> C) = generate G (B \<union> C)"
  by (metis assms generate_idem')

lemma (in group) generate_subgroup_id:
  assumes "subgroup H G"
  shows "generate G H = H"
  using assms generateI by auto

lemma (in group) generate_consistent':
  assumes "subgroup H G" "A \<subseteq> H"
  shows "\<forall>x \<in> A. generate G {x} = generate (G\<lparr>carrier := H\<rparr>) {x}"
  using generate_consistent assms by auto

lemma (in group) generate_singleton_one:
  assumes "generate G {a} = {\<one>}"
  shows "a = \<one>"
  using generate.incl[of a "{a}" G] assms by auto

lemma (in group) generate_inv_eq:
  assumes "a \<in> carrier G"
  shows "generate G {a} = generate G {inv a}"
  by (intro generate_eqI;
      use assms generate.inv[of a] generate.inv[of "inv a" "{inv a}" G] inv_inv[OF assms] in auto)

lemma (in group) generate_eq_imp_subset:
  assumes "generate G A = generate G B"
  shows "A \<subseteq> generate G B"
  using generate.incl assms by fast


text \<open>The neutral element does not play a role when generating a subgroup.\<close>

lemma (in group) generate_one_irrel:
  "generate G A = generate G (A \<union> {\<one>})"
proof
  show "generate G A \<subseteq> generate G (A \<union> {\<one>})" by (intro mono_generate, blast)
  show "generate G (A \<union> {\<one>}) \<subseteq> generate G A"
  proof(rule subsetI)
    show "x \<in> generate G A" if "x \<in> generate G (A \<union> {\<one>})" for x using that
      by (induction rule: generate.induct;
          use generate.one generate.incl generate.inv generate.eng in auto)
  qed
qed

lemma (in group) generate_one_irrel':
  "generate G A = generate G (A - {\<one>})"
  using generate_one_irrel by (metis Un_Diff_cancel2)

text \<open>Also, we can express the subgroup generated by a singleton with finite order using just its
powers up to its order.\<close>

lemma (in group) generate_nat_pow:
  assumes "ord a \<noteq> 0" "a \<in> carrier G"
  shows "generate G {a} = {a [^] k |k. k \<in> {0..ord a - 1}}"
  using assms generate_pow_nat ord_elems_inf_carrier by auto

lemma (in group) generate_nat_pow':
  assumes "ord a \<noteq> 0" "a \<in> carrier G"
  shows "generate G {a} = {a [^] k |k. k \<in> {1..ord a}}"
proof -
  have "{a [^] k |k. k \<in> {1..ord a}} = {a [^] k |k. k \<in> {0..ord a - 1}}"
  proof -
    have "a [^] k \<in> {a [^] k |k. k \<in> {0..ord a - 1}}" if "k \<in> {1..ord a}" for k
      using that pow_nat_mod_ord[OF assms(2, 1), of "ord a"] assms by (cases "k = ord a"; force)
    moreover have "a [^] k \<in> {a [^] k |k. k \<in> {1..ord a}}" if "k \<in> {0..ord a - 1}" for k
    proof(cases "k = 0")
      case True
      hence "a [^] k = a [^] ord a" using pow_ord_eq_1[OF assms(2)] by auto
      moreover have "ord a \<in> {1..ord a}"
        using assms unfolding atLeastAtMost_def atLeast_def atMost_def by auto
      ultimately show ?thesis by blast
    next
      case False
      then show ?thesis using that by auto
    qed 
    ultimately show ?thesis by blast
  qed
  with generate_nat_pow[OF assms] show ?thesis by simp
qed

end