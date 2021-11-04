(* Title: Examples/TTS_Foundations/Foundations/FNDS_Definite_Description.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Definite description operator\<close>
theory FNDS_Definite_Description
  imports Main
begin



subsection\<open>Definition and common properties\<close>

definition The_on 
  where "The_on U P = 
    (if \<exists>!x. x \<in> U \<and> P x then Some (THE x. x \<in> U \<and> P x) else None)"

syntax 
  "_The_on" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> 'a option" 
  ("(THE _ on _./ _)" [0, 0, 10] 10)
translations "THE x on U. P" \<rightleftharpoons> "CONST The_on U (\<lambda>x. P)"

print_translation \<open>
  [
    (
      \<^const_syntax>\<open>The_on\<close>, 
      fn _ => fn [Ut, Abs abs] =>
        let val (x, t) = Syntax_Trans.atomic_abs_tr' abs
        in Syntax.const \<^syntax_const>\<open>_The_on\<close> $ x $ Ut $ t end
    )
  ]
\<close>

lemma The_on_UNIV_eq_The:
  assumes "\<exists>!x. P x"
  obtains x where "(THE x on UNIV. P x) = Some x" and "(THE x. P x) = x"
  unfolding The_on_def by (simp add: assms)

lemma The_on_UNIV_None:
  assumes "\<not>(\<exists>!x. P x)"
  shows "(THE x on UNIV. P x) = None"
  unfolding The_on_def by (simp add: assms)

lemma The_on_eq_The:
  assumes "\<exists>!x. x \<in> U \<and> P x"
  obtains x where "(THE x on U. P x) = Some x" and "(THE x. x \<in> U \<and> P x) = x"
  unfolding The_on_def by (simp add: assms)

lemma The_on_None:
  assumes "\<not>(\<exists>!x. x \<in> U \<and> P x)"
  shows "(THE x on U. P x) = None"
  unfolding The_on_def by (auto simp: assms)

lemma The_on_Some_equality[intro]:
  assumes "a \<in> U" and "P a" and "\<And>x. x \<in> U \<Longrightarrow> P x \<Longrightarrow> x = a"
  shows "(THE x on U. P x) = Some a"
proof-
  from assms have "\<exists>!x. x \<in> U \<and> P x" by auto
  moreover have "(THE x. x \<in> U \<and> P x) = a" 
    apply standard using assms by blast+
  ultimately show ?thesis unfolding The_on_def by auto
qed  

lemma The_on_equality[intro]:
  assumes "a \<in> U" and "P a" and "\<And>x. x \<in> U \<Longrightarrow> P x \<Longrightarrow> x = a"
  shows "the (THE x on U. P x) = a"
  by (metis assms option.sel The_on_Some_equality)

lemma The_on_SomeI:
  assumes "a \<in> U" and "P a" and "\<And>x. x \<in> U \<Longrightarrow> P x \<Longrightarrow> x = a"
  obtains x where "(THE x on U. P x) = Some x" and "P x"
  using assms unfolding The_on_def by (meson that The_on_Some_equality)

lemma The_onI:
  assumes "a \<in> U" and "P a" and "\<And>x. x \<in> U \<Longrightarrow> P x \<Longrightarrow> x = a"
  shows "P (the (THE x on U. P x))"
  by (metis assms The_on_equality)

lemma The_on_SomeI': 
  assumes "\<exists>!x. x \<in> U \<and> P x" 
  obtains x where "(THE x on U. P x) = Some x" and "P x"
  by (metis assms The_on_SomeI)

lemma The_onI':
  assumes "\<exists>!x. x \<in> U \<and> P x" 
  shows "P (the (THE x on U. P x))"
  by (metis assms The_onI)

lemma The_on_SomeI2:
  assumes "a \<in> U" 
    and "P a" 
    and "\<And>x. x \<in> U \<Longrightarrow> P x \<Longrightarrow> x = a" 
    and "\<And>x. x \<in> U \<Longrightarrow> P x \<Longrightarrow> Q x"
  obtains x where "(THE x on U. P x) = Some x" and "Q x"
  using assms by blast

lemma The_on_I2:
  assumes "a \<in> U" 
    and "P a" 
    and "\<And>x. x \<in> U \<Longrightarrow> P x \<Longrightarrow> x = a" 
    and "\<And>x. x \<in> U \<Longrightarrow> P x \<Longrightarrow> Q x"
  shows "Q (the (THE x on U. P x))"
  by (metis assms The_on_equality)

lemma The_on_Some1I2:
  assumes "\<exists>!x. x \<in> U \<and> P x" and "\<And>x. x \<in> U \<Longrightarrow> P x \<Longrightarrow> Q x"
  obtains x where "(THE x on U. P x) = Some x" and "Q x"
  using assms by blast

lemma The_on1I2:
  assumes "\<exists>!x. x \<in> U \<and> P x" and "\<And>x. x \<in> U \<Longrightarrow> P x \<Longrightarrow> Q x"
  shows "Q (the (THE x on U. P x))"
  by (metis (mono_tags, hide_lams) The_on_I2 assms)

lemma The_on1_equality [elim?]: 
  assumes "\<exists>!x. P x" and "a \<in> U" and "P a" 
  shows "(THE x on U. P x) = Some a"
  using assms by blast

lemma the_sym_eq_trivial: 
  assumes "x \<in> U" 
  shows "(THE y on U. x = y) = Some x"
  using assms by blast



subsection\<open>Transfer rules\<close>

lemma The_on_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique A" "right_total A"
  shows "(rel_set A ===> (A ===> (=)) ===> rel_option A) The_on The_on"
proof(intro rel_funI)
  fix U and U' and P :: "'a \<Rightarrow> bool" and P' :: "'b \<Rightarrow> bool"
  assume UU'[transfer_rule]: "rel_set A U U'" 
    and PP'[transfer_rule]: "(A ===> (=)) P P'" 
  show "rel_option A (THE x on U. P x) (THE x on U'. P' x)"
  proof(cases \<open>\<exists>!x'. x' \<in> U' \<and> P' x'\<close>)
    case True show ?thesis
    proof-
      from True obtain x' where "x' \<in> U'" and "P' x'" by clarsimp
      with True have The_on': "(THE x on U'. P' x) = Some x'" 
        unfolding The_on_def by auto
      from assms(2) obtain x where [transfer_rule]: "A x x'"
        unfolding right_total_def by auto
      from True have "\<forall>y'\<in>U'. x' \<noteq> y' \<longrightarrow> (\<not>P' y')" 
        by (auto simp: \<open>x' \<in> U'\<close> \<open>P' x'\<close>)
      then have "\<forall>y\<in>U. x \<noteq> y \<longrightarrow> (\<not>P y)" by transfer
      moreover from \<open>P' x'\<close> have "P x" by transfer
      ultimately have "\<exists>!x. x \<in> U \<and> P x" 
        using UU' \<open>A x x'\<close> \<open>x' \<in> U'\<close> assms(1) 
        by (auto dest: bi_uniqueDl rel_setD2)
      moreover from \<open>x' \<in> U'\<close> have "x \<in> U" by transfer 
      ultimately have The_on: "(THE x on U. P x) = Some x" 
        using \<open>P x\<close> unfolding The_on_def by auto
      show ?thesis unfolding The_on The_on' by transfer_prover
    qed
  next
    case nux: False show ?thesis
    proof(cases \<open>\<exists>x'. x' \<in> U' \<and> P' x'\<close>)
      case True show ?thesis 
      proof-  
        from True obtain x' where "x' \<in> U'" and "P' x'" by clarsimp
        with nux True obtain y' where "y' \<in> U'" and "P' y'" and "x' \<noteq> y'" 
          by auto
        from assms(2) \<open>P' x'\<close> obtain x where [transfer_rule]: "A x x'"
          unfolding right_total_def by auto
        from assms(2) \<open>P' y'\<close> obtain y where [transfer_rule]: "A y y'" 
          unfolding right_total_def by auto
        from \<open>P' x'\<close> have "P x" by transfer
        moreover from \<open>P' y'\<close> have "P y" by transfer
        moreover from \<open>x' \<noteq> y'\<close> have "x \<noteq> y" by transfer
        ultimately have "\<nexists>!x. x \<in> U \<and> P x" 
          apply transfer 
          using UU' \<open>A x x'\<close> \<open>A y y'\<close> \<open>x' \<in> U'\<close> \<open>y' \<in> U'\<close> assms(1) 
          by (blast dest: bi_uniqueDl rel_setD2)
        then show ?thesis unfolding The_on_def by (auto simp: nux)
      qed
    next
      case False then show ?thesis
        unfolding The_on_def 
        using PP' UU' by (fastforce dest: rel_funD rel_setD1)
    qed
  qed
qed

text\<open>\newpage\<close>

end