subsection \<open>Determined games\<close>

theory GaleStewartDeterminedGames
  imports GaleStewartDefensiveStrategies
begin

locale closed_GSgame = GSgame +
  assumes closed:"e \<in> A \<Longrightarrow> \<exists> p. lprefix (llist_of p) e \<and> (\<forall> e'. lprefix (llist_of p) e' \<longrightarrow> llength e' = 2*N \<longrightarrow> e' \<in> A)"

(* Perhaps a misnomer, GSgames are supposed to be infinite, but this is very much the GS variation
   of finite games, as definitions still use coinductive lists rather than the more common
   inductive (and finite) ones. *)
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

text \<open> By proving that every position is determined, this proves that every game is determined
       (since a game is determined if its initial position [] is) \<close>
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
lemma empty_position: "position []" using zero_enat_def position_def by auto
lemmas every_game_is_determined = every_position_is_determined[OF empty_position]


text \<open> We expect that this theorem can be easier to apply without the 'position p' requirement,
       so we present that theorem as well. \<close>
lemma every_position_has_winning_strategy:
  shows "(\<exists> \<sigma>. strategy_winning_by_Even \<sigma> p) \<or> (\<exists> \<sigma>. strategy_winning_by_Odd \<sigma> p)" (is "?we \<or> ?wo")
proof(cases "position p")
  case True
  then show ?thesis using every_position_is_determined by blast
next
  case False
  hence "2 * N \<le> enat (length p)" unfolding position_def by force
  from induced_play_lprefix_non_positions[OF this]
  show ?thesis unfolding strategy_winning_by_Even_def strategy_winning_by_Odd_def by simp
qed

end

end