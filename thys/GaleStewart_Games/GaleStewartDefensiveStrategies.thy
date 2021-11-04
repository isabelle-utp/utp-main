subsection \<open>Defensive strategies\<close>

text \<open> A strategy is defensive if a player can avoid reaching winning positions.
       If the opponent is not already in a winning position, such defensive strategies exist.
       In closed games, a defensive strategy is winning for the closed player,
       so these strategies are a crucial step towards proving that such games are determined.
        \<close>
theory GaleStewartDefensiveStrategies
  imports GaleStewartGames
begin

context GSgame
begin

definition move_defensive_by_Even where
  "move_defensive_by_Even m p \<equiv> even (length p) \<longrightarrow> \<not> winning_position_Odd (p @ [m])"
definition move_defensive_by_Odd where
  "move_defensive_by_Odd m p  \<equiv> odd (length p) \<longrightarrow> \<not> winning_position_Even (p @ [m])"

(* This was a tricky part of the proof, it required explicit use of the choice theorem *)
lemma defensive_move_exists_for_Even:
assumes [intro]:"position p"
shows "winning_position_Odd p \<or> (\<exists> m. move_defensive_by_Even m p)" (is "?w \<or> ?d")
proof(cases "length p = 2*N \<or> odd (length p)")
  case False
  hence pl[intro]:"length p < 2*N"
    and ev[intro]:"even (length p)" using assms[unfolded position_def] by auto
  show ?thesis proof(rule impI[of "\<not> ?d \<longrightarrow> \<not> ?w \<longrightarrow> False", rule_format], force)
    assume not_def:"\<not> ?d"
    from not_def[unfolded move_defensive_by_Even_def]
    have "\<forall> m. \<exists>\<sigma>. strategy_winning_by_Odd \<sigma> (p @ [m])" by blast
    from choice[OF this] obtain \<sigma>\<^sub>o where
      str_Odd:"\<And> m. strategy_winning_by_Odd (\<sigma>\<^sub>o m) (p @ [m])" by blast
    define \<sigma> where "\<sigma> p' = \<sigma>\<^sub>o (p' ! length p) p'" for p'
    assume not_win:"\<not> ?w"
    from not_win[unfolded move_defensive_by_Even_def strategy_winning_by_Odd_def]
    obtain \<sigma>\<^sub>e where
      str_Even:"induced_play (joint_strategy \<sigma>\<^sub>e \<sigma>) p \<in> A"
      (is "?pe p \<in> A")
           by blast
    let ?pnext = "(p @ [joint_strategy \<sigma>\<^sub>e \<sigma> p])"
    { fix p' m
      assume "prefix (p @ [m]) p'"
      hence "(p' ! length p) = m"
        unfolding prefix_def by auto
    }
    hence eq_a:"\<forall> p'. prefix ?pnext p' \<longrightarrow> p' @ [joint_strategy \<sigma>\<^sub>e \<sigma> p'] =
                                    p' @ [joint_strategy \<sigma>\<^sub>e (\<sigma>\<^sub>o (joint_strategy \<sigma>\<^sub>e \<sigma> p)) p']"
      unfolding joint_strategy_def \<sigma>_def by auto
    have simps:"?pe p = ?pe (p @ [joint_strategy \<sigma>\<^sub>e \<sigma> p])"
      unfolding induced_play_def by auto
    from str_Even str_Odd[of "joint_strategy \<sigma>\<^sub>e \<sigma> p", unfolded strategy_winning_by_Odd_def, rule_format, of "\<sigma>\<^sub>e"]
         induced_play_eq[OF eq_a]
    show False unfolding simps by auto
  qed
qed (auto simp: move_defensive_by_Even_def strategy_winning_by_Even_def position_maxlength_cannotbe_augmented)

(* This is a repetition of the proof for defensive_move_exists_for_Even *)
lemma defensive_move_exists_for_Odd:
assumes [intro]:"position p"
shows "winning_position_Even p \<or> (\<exists> m. move_defensive_by_Odd m p)" (is "?w \<or> ?d")
proof(cases "length p = 2*N \<or> even (length p)")
  case False
  hence pl[intro]:"length p < 2*N"
    and ev[intro]:"odd (length p)" using assms[unfolded position_def] by auto
  show ?thesis proof(rule impI[of "\<not> ?d \<longrightarrow> \<not> ?w \<longrightarrow> False", rule_format], force)
    assume not_def:"\<not> ?d"
    from not_def[unfolded move_defensive_by_Odd_def]
    have "\<forall> m. \<exists>\<sigma>. strategy_winning_by_Even \<sigma> (p @ [m])" by blast
    from choice[OF this] obtain \<sigma>\<^sub>e where
      str_Even:"\<And> m. strategy_winning_by_Even (\<sigma>\<^sub>e m) (p @ [m])" by blast
    define \<sigma> where "\<sigma> p' = \<sigma>\<^sub>e (p' ! length p) p'" for p'
    assume not_win:"\<not> ?w"
    from not_win[unfolded move_defensive_by_Odd_def strategy_winning_by_Even_def]
    obtain \<sigma>\<^sub>o where
      str_Odd:"induced_play (joint_strategy \<sigma> \<sigma>\<^sub>o) p \<notin> A"
      (is "?pe p \<notin> A")
           by blast
    let ?strat = "joint_strategy \<sigma> \<sigma>\<^sub>o"
    let ?pnext = "(p @ [?strat p])"
    { fix p' m
      assume "prefix (p @ [m]) p'"
      hence "(p' ! length p) = m"
        unfolding prefix_def by auto
    }
    hence eq_a:"\<forall> p'. prefix ?pnext p' \<longrightarrow> p' @ [?strat p'] =
                                    p' @ [joint_strategy (\<sigma>\<^sub>e (?strat p)) \<sigma>\<^sub>o p']"
      unfolding joint_strategy_def \<sigma>_def by auto
    have simps:"?pe p = ?pe (p @ [?strat p])"
      unfolding induced_play_def by auto
    from str_Odd str_Even[of "?strat p", unfolded strategy_winning_by_Even_def, rule_format]
         induced_play_eq[OF eq_a]
    show False unfolding simps by auto
  qed
qed (auto simp: move_defensive_by_Odd_def strategy_winning_by_Odd_def position_maxlength_cannotbe_augmented)

definition defensive_strategy_Even where
"defensive_strategy_Even p \<equiv> SOME m. move_defensive_by_Even m p"
definition defensive_strategy_Odd where
"defensive_strategy_Odd p \<equiv> SOME m. move_defensive_by_Odd m p"

lemma position_augment:
  assumes "position ((augment_list f ^^ n) p)"
  shows "position p"
  using assms length_augment_list[of n f p] unfolding position_def
  by fastforce

lemma defensive_strategy_Odd:
  assumes "\<not> winning_position_Even p"
  shows "\<not> winning_position_Even (((augment_list (joint_strategy \<sigma>\<^sub>e defensive_strategy_Odd)) ^^ n) p)"
proof -
  show ?thesis using assms proof(induct n arbitrary:p)
    case (Suc n)
    show ?case proof(cases "position p")
      case True
      from Suc.prems defensive_move_exists_for_Odd[OF True] defensive_strategy_Odd_def someI
      have "move_defensive_by_Odd (defensive_strategy_Odd p) p" by metis
      from this[unfolded move_defensive_by_Odd_def] Suc.prems
           non_winning_moves_remains_non_winning_Even[of p]
      have "\<not> winning_position_Even (p @ [joint_strategy \<sigma>\<^sub>e defensive_strategy_Odd p])"
        by (simp add:  joint_strategy_def True) 
      with Suc.hyps[of "p @ [joint_strategy \<sigma>\<^sub>e defensive_strategy_Odd p]"]
      show ?thesis unfolding funpow_Suc_right comp_def by fastforce
    qed (insert position_augment,blast)
  qed auto
qed

lemma defensive_strategy_Even:
  assumes "\<not> winning_position_Odd p"
  shows "\<not> winning_position_Odd (((augment_list (joint_strategy defensive_strategy_Even \<sigma>\<^sub>o)) ^^ n) p)"
proof -
  show ?thesis using assms proof(induct n arbitrary:p)
    case (Suc n)
    show ?case proof(cases "position p")
      case True
      from Suc.prems defensive_move_exists_for_Even[OF True] defensive_strategy_Even_def someI
      have "move_defensive_by_Even (defensive_strategy_Even p) p" by metis
      from this[unfolded move_defensive_by_Even_def] Suc.prems
           non_winning_moves_remains_non_winning_Odd[of p]
      have "\<not> winning_position_Odd (p @ [joint_strategy defensive_strategy_Even \<sigma>\<^sub>o p])"
        by (simp add: joint_strategy_def True) 
      with Suc.hyps[of "p @ [joint_strategy defensive_strategy_Even \<sigma>\<^sub>o p]"]
      show ?thesis unfolding funpow_Suc_right comp_def by fastforce
    qed (insert position_augment,blast)
  qed auto
qed


end

locale closed_GSgame = GSgame +
  assumes closed:"e \<in> A \<Longrightarrow> \<exists> p. lprefix (llist_of p) e \<and> (\<forall> e'. lprefix (llist_of p) e' \<longrightarrow> llength e' = 2*N \<longrightarrow> e' \<in> A)"

(* Perhaps a misnomer, GSgames are supposed to be infinite ... *)
locale finite_GSgame = GSgame +
  assumes fin:"N \<noteq> \<infinity>"
begin

text \<open> Finite games are closed games. As a corollary to the GS theorem, this lets us conclude that finite games are determined. \<close>
sublocale closed_GSgame
proof
  fix e assume eA:"e \<in> A"
  let ?p = "list_of e"
  from eA have len:"llength e = 2*N" using length by blast
  with fin have p:"llist_of ?p = e"
    by (metis llist_of_list_of mult_2 not_lfinite_llength plus_eq_infty_iff_enat)
  hence pfx:"lprefix (llist_of ?p) e" by auto
  { fix e'
    assume "lprefix (llist_of ?p) e'" "llength e' = 2 * N"
    hence "e' = e" using len by (metis lprefix_llength_eq_imp_eq p)
    with eA have "e' \<in> A" by simp
  }
  with pfx show "\<exists>p. lprefix (llist_of p) e \<and> (\<forall>e'. lprefix (llist_of p) e' \<longrightarrow> llength e' = 2 * N \<longrightarrow> e' \<in> A)"
    by blast
qed
end

context closed_GSgame begin
lemma never_winning_is_losing_even:
  assumes "position p" "\<forall> n. \<not> winning_position_Even (((augment_list \<sigma>) ^^ n) p)"
  shows "induced_play \<sigma> p \<notin> A"
proof
  assume "induced_play \<sigma> p \<in> A"
  from closed[OF this] obtain p' where
    p':"lprefix (llist_of p') (induced_play \<sigma> p)"
    "\<And> e. lprefix (llist_of p') e \<Longrightarrow> llength e = 2 * N \<Longrightarrow> e \<in> A" by blast
  from lprefix_llength_le[OF p'(1)] have lp':"llength (llist_of p') \<le> 2 * N" by auto
  show False proof (cases "length p' \<le> length p")
    case True
    hence "llength (llist_of p') \<le> llength (llist_of p)" by auto
    from lprefix_llength_lprefix[OF p'(1) _ this]
      induced_play_is_lprefix[OF assms(1)]
      lprefix_trans
    have pref:"lprefix (llist_of p') (induced_play strat p)" for strat by blast
    from assms(2)[rule_format,of 0] assms(1) have "\<not> strategy_winning_by_Even \<sigma> p" for \<sigma> by auto
    from this[unfolded strategy_winning_by_Even_def] obtain strat where
      strat:"induced_play strat p \<notin> A" by auto
    from strat p'(2)[OF pref] show False by simp
  next
    case False
    let ?n = "length p' - length p"
    let ?pos = "(augment_list \<sigma> ^^ ?n) p"
    from False have "length p' \<ge> length p" by auto
    hence [simp]:"length ?pos = length p'"
      by (auto simp:length_augment_list)
    hence pos[intro]:"position ?pos"
      using False lp'(1) unfolding position_def by auto
    have "llist_of p' = llist_of ?pos"
      using p'(1)
      by(intro lprefix_antisym[OF lprefix_llength_lprefix lprefix_llength_lprefix],auto)
    hence p'_pos:"p' = ?pos" by simp
    from assms(2)[rule_format,of ?n] assms(1) have "\<not> strategy_winning_by_Even \<sigma> ?pos" for \<sigma> by auto
    from this[unfolded strategy_winning_by_Even_def] obtain strat where
      strat:"induced_play strat ?pos \<notin> A" by auto
    from p'_pos induced_play_is_lprefix[OF pos, of strat]
    have pref:"lprefix (llist_of p') (induced_play strat ?pos)" by simp
    with p'(2)[OF pref] strat show False by simp
  qed
qed

lemma every_position_is_determined:
  assumes "position p"
  shows "winning_position_Even p \<or> winning_position_Odd p" (is "?we \<or> ?wo")
proof(rule impI[of "\<not> ?we \<longrightarrow> \<not> ?wo \<longrightarrow> False",rule_format],force)
  assume "\<not> ?we"
  from defensive_strategy_Odd[OF this] never_winning_is_losing_even[OF assms]
  have js_no:"induced_play
         (joint_strategy s defensive_strategy_Odd) p \<notin> A" for s
    by auto
  assume "\<not> ?wo"
  from this[unfolded strategy_winning_by_Odd_def] assms
  have "\<exists> s. induced_play
         (joint_strategy s defensive_strategy_Odd) p \<in> A" by simp
  thus False using js_no by simp
qed

end

end