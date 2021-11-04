(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Further results about ordinal numbers\<close>
theory CZH_Sets_Ordinals
  imports 
    CZH_Sets_Nat
    CZH_Sets_IF
    Complex_Main
begin



subsection\<open>Background\<close>


text\<open>
The subsection presents several results about ordinal 
numbers. The primary general reference for this section 
is \cite{takeuti_introduction_1971}.
\<close>

lemmas [intro] = Limit_is_Ord Ord_in_Ord



subsection\<open>Further ordinal arithmetic and inequalities\<close>


lemma Ord_succ_mono:
  assumes "Ord \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "succ \<alpha> \<in>\<^sub>\<circ> succ \<beta>"
proof-
  from assms have "Ord \<alpha>" by blast
  from assms \<open>Ord \<alpha>\<close> have "\<alpha> < \<beta>" by (auto dest: Ord_mem_iff_lt)
  from assms(1,2) this have "succ \<alpha> < succ \<beta>"
    by (meson assms \<open>Ord \<alpha>\<close> Ord_linear2 Ord_succ leD le_succ_iff)
  with assms(1) \<open>Ord \<alpha>\<close> Ord_mem_iff_lt show "succ \<alpha> \<in>\<^sub>\<circ> succ \<beta>" by blast
qed

lemma Limit_right_Limit_mult:
  \<comment>\<open>Based on Theorem 8.23 in \cite{takeuti_introduction_1971}.\<close>
  assumes "Ord \<alpha>" and "Limit \<beta>" and "0 \<in>\<^sub>\<circ> \<alpha>" 
  shows "Limit (\<alpha> * \<beta>)"
proof-
  have \<alpha>\<beta>: "\<alpha> * \<beta> = (\<Union>\<^sub>\<circ>\<xi>\<in>\<^sub>\<circ>\<beta>. \<alpha> * \<xi>)" by (rule mult_Limit[OF assms(2), of \<alpha>])
  from assms(1,2) Ord_mult have "Ord (\<alpha> * \<beta>)" by blast
  then show ?thesis 
  proof(cases rule: Ord_cases)
    case (succ \<gamma>)
    from succ(1) have "\<gamma> \<in>\<^sub>\<circ> \<alpha> * \<beta>" unfolding succ(2)[symmetric] by simp
    then obtain \<xi> where "\<xi> \<in>\<^sub>\<circ> \<beta>" and "\<gamma> \<in>\<^sub>\<circ> \<alpha> * \<xi>" unfolding \<alpha>\<beta> by auto
    moreover with assms(2) have "Ord \<xi>" by auto
    ultimately have s\<gamma>_s\<alpha>\<xi>: "succ \<gamma> \<in>\<^sub>\<circ> succ (\<alpha> * \<xi>)"
      using assms(1) Ord_succ_mono by simp
    from assms(2,3) have "succ (\<alpha> * \<xi>) \<subseteq>\<^sub>\<circ> \<alpha> * \<xi> + \<alpha>" 
      unfolding succ_eq_add1 by force
    with s\<gamma>_s\<alpha>\<xi> have "succ \<gamma> \<in>\<^sub>\<circ> \<alpha> * succ \<xi>" 
      unfolding mult_succ[symmetric] by auto
    moreover have "succ \<xi> \<in>\<^sub>\<circ> \<beta>" 
      by (simp add: succ_in_Limit_iff \<open>\<xi> \<in>\<^sub>\<circ> \<beta>\<close> assms(2))
    ultimately have "succ \<gamma> \<in>\<^sub>\<circ> \<alpha> * \<beta>" unfolding \<alpha>\<beta> by force
    with succ(2) show ?thesis by simp
  qed (use assms(2,3) in auto)
qed

lemma Limit_left_Limit_mult:
  assumes "Limit \<alpha>" and "Ord \<beta>" and "0 \<in>\<^sub>\<circ> \<beta>" 
  shows "Limit (\<alpha> * \<beta>)"
proof(cases \<open>Limit \<beta>\<close>)
  case False
  then obtain \<beta>' where "Ord \<beta>'" and \<beta>_def: "\<beta> = succ \<beta>'" 
    by (metis Ord_cases assms(2,3) eq0_iff)
  have \<alpha>_s\<beta>': "\<alpha> * succ \<beta>' = \<alpha> * \<beta>' + \<alpha>" by (simp add: mult_succ)
  from assms(1) have "Limit (\<alpha> * \<beta>' + \<alpha>)" by (simp add: Limit_is_Ord \<open>Ord \<beta>'\<close>)
  then show "Limit (\<alpha> * \<beta>)" unfolding \<beta>_def \<alpha>_s\<beta>' by simp
qed (use assms in \<open>auto simp: Limit_def dest: Limit_right_Limit_mult\<close>)

lemma zero_if_Limit_eq_Limit_plus_vnat:
  assumes "Limit \<alpha>" and "Limit \<beta>" and "\<alpha> = \<beta> + n" and "n \<in>\<^sub>\<circ> \<omega>"
  shows "n = 0"
proof(rule ccontr)
  assume prems: "n \<noteq> 0"
  from assms(1,2,4) have "Ord \<alpha>" and "Ord \<beta>" and "Ord 0" and "Ord n" by auto
  have "0 \<in>\<^sub>\<circ> n" by (simp add: mem_0_Ord prems assms(4)) 
  with assms(4) obtain m where n_def: "n = succ m" by (auto elim: omega_prev)
  from assms(1,3) show False by (simp add: n_def plus_V_succ_right)
qed

lemma Ord_vsubset_closed: 
  assumes "Ord \<alpha>" and "Ord \<gamma>" and "\<alpha> \<subseteq>\<^sub>\<circ> \<beta>" and "\<beta> \<in>\<^sub>\<circ> \<gamma>" 
  shows "\<alpha> \<in>\<^sub>\<circ> \<gamma>" 
proof-
  from assms have "Ord \<beta>" by auto
  with assms show ?thesis by (simp add: Ord_mem_iff_lt)
qed

lemma
  \<comment>\<open>Based on Exercise 1, page 53 in \cite{takeuti_introduction_1971}.\<close>
  assumes "Ord \<alpha>" and "Ord \<gamma>" and "\<alpha> + \<beta> \<in>\<^sub>\<circ> \<gamma>" 
  shows Ord_plus_Ord_closed_augend: "\<alpha> \<in>\<^sub>\<circ> \<gamma>" 
    and Ord_plus_Ord_closed_addend: "\<beta> \<in>\<^sub>\<circ> \<gamma>"
proof-
  from assms have "\<alpha> + \<beta> \<in>\<^sub>\<circ> \<alpha> + \<gamma>" by (meson vsubsetD add_le_left)
  from add_mem_right_cancel[THEN iffD1, OF this] show "\<beta> \<in>\<^sub>\<circ> \<gamma>" .
  from assms have "\<alpha> \<subseteq>\<^sub>\<circ> \<alpha> + \<beta>" by simp
  from Ord_vsubset_closed[OF assms(1,2) this assms(3)] show "\<alpha> \<in>\<^sub>\<circ> \<gamma>" .
qed

lemma Ord_ex1_Limit_plus_in_omega:
  \<comment>\<open>Based on Theorem 8.13 in \cite{takeuti_introduction_1971}.\<close>
  assumes "Ord \<alpha>" and "\<omega> \<subseteq>\<^sub>\<circ> \<alpha>"
  shows "\<exists>!\<beta>. \<exists>!n. n \<in>\<^sub>\<circ> \<omega> \<and> Limit \<beta> \<and> \<alpha> = \<beta> + n"
proof-
  let ?A = \<open>set {\<gamma>. Limit \<gamma> \<and> \<gamma> \<subseteq>\<^sub>\<circ> \<alpha>}\<close>
  have small[simp]: "small {\<gamma>. Limit \<gamma> \<and> \<gamma> \<subseteq>\<^sub>\<circ> \<alpha>}"
  proof-
    from Ord_mem_iff_lt  have "{\<gamma>. Limit \<gamma> \<and> \<gamma> \<subseteq>\<^sub>\<circ> \<alpha>} \<subseteq> elts (succ \<alpha>)"
      by (auto dest: order.not_eq_order_implies_strict intro: assms(1))
    then show "small {\<gamma>. Limit \<gamma> \<and> \<gamma> \<subseteq>\<^sub>\<circ> \<alpha>}" by (meson down)
  qed
  let ?\<beta> = \<open>\<Union>\<^sub>\<circ>?A\<close>
  have "?\<beta> \<subseteq>\<^sub>\<circ> \<alpha>" by auto
  moreover have L_\<beta>: "Limit ?\<beta>"
  proof(subst Limit_def, intro conjI allI impI)
    show "Ord ?\<beta>" by (fastforce intro: Ord_Sup)
    from assms(2) show "0 \<in>\<^sub>\<circ> ?\<beta>" by auto
    fix y assume "y \<in>\<^sub>\<circ> ?\<beta>"
    then obtain \<gamma> where "y \<in>\<^sub>\<circ> \<gamma>" and "\<gamma> \<in>\<^sub>\<circ> ?A" by clarsimp
    then show "succ y \<in>\<^sub>\<circ> ?\<beta>" by (auto simp: succ_in_Limit_iff)
  qed
  ultimately obtain \<gamma> where "Ord \<gamma>" and \<alpha>_def: "\<alpha> = ?\<beta> + \<gamma>"
    by (metis assms(1) le_Ord_diff Limit_is_Ord)
  from L_\<beta> have L_\<beta>\<omega>: "Limit (?\<beta> + \<omega>)" by (blast intro: Limit_add_Limit)
  have "\<gamma> \<subset>\<^sub>\<circ> \<omega>"
  proof(rule ccontr)
    assume "~\<gamma> \<subset>\<^sub>\<circ> \<omega>"
    with \<open>Ord \<gamma>\<close> Ord_linear2 have "\<omega> \<subseteq>\<^sub>\<circ> \<gamma>" by auto
    then obtain \<delta> where \<gamma>_def: "\<gamma> = \<omega> + \<delta>" 
      by (blast dest: Ord_odiff_eq intro: \<open>Ord \<gamma>\<close>)
    from \<alpha>_def have "\<alpha> = (?\<beta> + \<omega>) + \<delta>" by (simp add: add.assoc \<gamma>_def)
    then have "?\<beta> + \<omega> \<subseteq>\<^sub>\<circ> \<alpha>" by (metis add_le_cancel_left0)
    with L_\<beta>\<omega> have "?\<beta> + \<omega> \<subseteq>\<^sub>\<circ> ?\<beta>" by auto
    with add_le_cancel_left[of ?\<beta> \<omega> 0, THEN iffD1] show False by simp
  qed
  with \<alpha>_def have "\<gamma> \<in>\<^sub>\<circ> \<omega>" by (auto simp: Ord_mem_iff_lt \<open>Ord \<gamma>\<close>)
  show ?thesis
  proof
    (
      intro ex1I conjI; 
      (elim conjE ex1E allE conjE impE | tactic\<open>all_tac\<close>);
      (intro conjI | tactic\<open>all_tac\<close>)
    )
    show "\<gamma> \<in>\<^sub>\<circ> \<omega>" by (rule \<open>\<gamma> \<in>\<^sub>\<circ> \<omega>\<close>)
    show "Limit ?\<beta>" by (rule \<open>Limit ?\<beta>\<close>)
    show "\<alpha> = ?\<beta> + \<gamma>" by (rule \<alpha>_def)
    from \<alpha>_def show "\<alpha> = ?\<beta> + n \<Longrightarrow> n = \<gamma>" for n by auto
    show "n \<in>\<^sub>\<circ> \<omega> \<Longrightarrow> Limit \<beta> \<Longrightarrow> \<alpha> = \<beta> + n \<Longrightarrow> \<beta> = ?\<beta>" for n \<beta>
    proof-
      assume prems: "n \<in>\<^sub>\<circ> \<omega>" "Limit \<beta>" "\<alpha> = \<beta> + n"
      from L_\<beta> prems(2,3) have "\<beta> \<subseteq>\<^sub>\<circ> ?\<beta>" by auto
      then obtain \<eta> where \<beta>_def: "?\<beta> = \<beta> + \<eta>" and "Ord \<eta>" 
        by (metis (lifting) L_\<beta> Limit_is_Ord le_Ord_diff prems(2))
      moreover have "\<eta> \<in>\<^sub>\<circ> \<omega>"
      proof-
        from \<alpha>_def \<beta>_def have "\<beta> + \<eta> + \<gamma> = \<beta> + n" by (simp add: prems(3))
        then have "\<eta> + \<gamma> = n" by (simp add: add.assoc)
        with \<open>\<gamma> \<in>\<^sub>\<circ> \<omega>\<close> \<open>n \<in>\<^sub>\<circ> \<omega>\<close> \<open>Ord \<gamma>\<close> show "\<eta> \<in>\<^sub>\<circ> \<omega>"
          by (blast intro: calculation(2) Ord_plus_Ord_closed_augend)
      qed
      ultimately show ?thesis 
        using prems(2) L_\<beta> by (force dest: zero_if_Limit_eq_Limit_plus_vnat)
    qed      
  qed 
qed

lemma not_Limit_if_in_Limit_plus_omega:
  assumes "Limit \<alpha>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>" and "\<beta> \<in>\<^sub>\<circ> \<alpha> + \<omega>"
  shows "~Limit \<beta>"
proof-
  from assms Ord_add have "Ord \<beta>" by blast
  show ?thesis
    using assms(3)
  proof(cases rule: mem_plus_V_E)
    case 1 with mem_not_sym show ?thesis by (auto simp: assms(2,3))
  next
    case (2 z)
    from zero_if_Limit_eq_Limit_plus_vnat[OF _ assms(1) 2(2) 2(1)] 2(2) assms(2) 
    show ?thesis  
      by force
  qed
qed

lemma Limit_plus_omega_vsubset_Limit: 
  assumes "Limit \<alpha>" and "Limit \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<alpha> + \<omega> \<subseteq>\<^sub>\<circ> \<beta>"
proof- 
  from assms(1) have L\<alpha>\<omega>: "Limit (\<alpha> + \<omega>)" by (simp add: Limit_is_Ord)
  from not_Limit_if_in_Limit_plus_omega[OF assms(1,3)] assms(2) have
    "\<beta> \<notin>\<^sub>\<circ> \<alpha> + \<omega>"
    by clarsimp
  with assms(2) have "~\<beta> \<subset>\<^sub>\<circ> \<alpha> + \<omega>"
    by (blast intro: L\<alpha>\<omega> dest: Ord_mem_iff_lt Limit_is_Ord)
  then show "\<alpha> + \<omega> \<subseteq>\<^sub>\<circ> \<beta>" by (meson assms L\<alpha>\<omega> Limit_is_Ord Ord_linear2)
qed

lemma Limit_plus_nat_in_Limit:
  assumes "Limit \<alpha>" and "Limit \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<alpha> + a\<^sub>\<nat> \<in>\<^sub>\<circ> \<beta>"
  using assms Limit_plus_omega_vsubset_Limit[OF assms] by auto

lemma omega2_vsubset_Limit:
  assumes "Limit \<alpha>" and "\<omega> \<in>\<^sub>\<circ> \<alpha>"
  shows "\<omega> + \<omega> \<subseteq>\<^sub>\<circ> \<alpha>"
  using assms by (simp add: Limit_plus_omega_vsubset_Limit)

text\<open>\newpage\<close>

end