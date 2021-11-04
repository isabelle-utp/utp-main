section \<open>Gale Stewart Games\<close>

text \<open>Gale Stewart Games are infinite two player games.\<close>
(* [Gale & Stewart 1953] David Gale, F. M. Stewart, Infinite games with perfect information,
   Contributions to the Theory of Games II, ed. H. W. Kuhn and A. W. Tucker,
   Annals of Mathematics Studies 28, Princeton University Press (1953), pp 245–266. *)

theory GaleStewartGames
  imports AlternatingLists MorePrefix MoreENat
begin

subsection \<open>Basic definitions and their properties.\<close>

text \<open>A GSgame G(A) is defined by a set of sequences that denote the winning games for the first
      player. Our notion of GSgames generalizes both finite and infinite games by setting a game length.
      Note that the type of n is 'enat' (extended nat): either a nonnegative integer or infinity.
      Our only requirement on GSgames is that the winning games must have the length as specified
      as the length of the game. This helps certain theorems about winning look a bit more natural.\<close>

locale GSgame =
  fixes A N
  assumes length:"\<forall>e\<in>A. llength e = 2*N"
begin

text \<open>A position is a finite sequence of valid moves.\<close>
definition "position" where
  "position (e::'a list) \<equiv> length e \<le> 2*N"

lemma position_maxlength_cannotbe_augmented:
assumes "length p = 2*N"
shows "\<not> position (p @ [m])"
 by (auto simp:position_def assms[symmetric])

text \<open>A play is a sequence of valid moves of the right length.\<close>
definition "play" where
  "play (e::'a llist) \<equiv> llength e = 2*N"

lemma plays_are_positions_conv:
  shows "play (llist_of p) \<longleftrightarrow> position p \<and> length p = 2*N" 
unfolding play_def position_def by auto

lemma finite_plays_are_positions:
  assumes "play p" "lfinite p"
  shows "position (list_of p)"
using assms 
unfolding play_def position_def by (cases "lfinite p";auto simp:length_list_of)

end

text \<open>We call our players Even and Odd, where Even makes the first move.
      This means that Even is to make moves on plays of even length, and Odd on the others.
      This corresponds nicely to Even making all the moves in an even position, as
      the `nth' and `lnth' functions as predefined in Isabelle's library count from 0.
      In literature the players are sometimes called I and II.\<close>

text \<open>A strategy for Even/Odd is simply a function that takes a position of even/odd length and
      returns a move. We use total functions for strategies. This means that their Isabelle-type
      determines that it is a strategy. Consequently, we do not have a definition of 'strategy'.
      Nevertheless, we will use $\sigma$ as a letter to indicate when something is a strategy.
      We can combine two strategies into one function, which gives a collective strategy that
      we will refer to as the joint strategy.\<close>

definition joint_strategy  :: "('b list \<Rightarrow> 'a) \<Rightarrow> ('b list \<Rightarrow> 'a) \<Rightarrow> ('b list \<Rightarrow> 'a)" where
  "joint_strategy \<sigma>\<^sub>e \<sigma>\<^sub>o p = (if even (length p) then \<sigma>\<^sub>e p else \<sigma>\<^sub>o p)"

text \<open>Following a strategy leads to an infinite sequence of moves.
      Note that we are not in the context of 'GSGame' where 'N' determines the length of our plays:
      we just let sequences go on ad infinitum here.
      Rather than reasoning about our own recursive definitions,
      we build this infinite sequence by reusing definitions that are already in place.
      We do this by first defining all prefixes of the infinite sequence we are interested in.
      This gives an infinite list such that the nth element is of length n.
      Note that this definition allows us to talk about how a strategy would continue if it were
      played from an arbitrary position (not necessarily one that is reached via that strategy). \<close>

definition strategy_progression where
  "strategy_progression \<sigma> p = lappend (llist_of (prefixes p)) (ltl (iterates (augment_list \<sigma>) p))"

lemma induced_play_infinite:
  "\<not> lfinite (strategy_progression \<sigma> p)"
unfolding strategy_progression_def by auto

lemma plays_from_strategy_lengths[simp]:
  "length (strategy_progression \<sigma> p $ i) = i"
proof(induct i)
  case 0
  then show ?case by(cases p;auto simp:strategy_progression_def lnth_lappend take_map ltake_lappend)
next
  case (Suc i)
  then show ?case
    by (cases "i<length p") (auto simp:strategy_progression_def lnth_lappend length_augment_list tl_prefixes_idx)
qed

lemma length_plays_from_strategy[simp]:
  "llength (strategy_progression \<sigma> p) = \<infinity>"
  unfolding strategy_progression_def by auto
lemma length_ltl_plays_from_strategy[simp]:
  "llength (ltl (strategy_progression \<sigma> p)) = \<infinity>"
  unfolding strategy_progression_def by auto

lemma plays_from_strategy_chain_Suc:
  shows "prefix (strategy_progression \<sigma> p  $  n) (strategy_progression \<sigma> p  $  Suc n)"
  unfolding strategy_progression_def
  by (auto simp:take_Suc_prefix nth_prefixes lnth_lappend nth_prefixes_is_prefix_tl
                augment_list_prefix)

lemma plays_from_strategy_chain:
  shows "n \<le> m \<Longrightarrow> prefix (strategy_progression \<sigma> p  $  n) (strategy_progression \<sigma> p  $  m)"
proof (induct "m-n" arbitrary:m n)
  case (Suc x)
  hence [simp]:"Suc (x + n) = m" by auto
  from Suc.hyps(2) 
    prefix_order.order.trans[OF Suc.hyps(1)[of "x + n" n] plays_from_strategy_chain_Suc[of _ _ "x+n"]]
  show ?case by auto
qed auto

lemma plays_from_strategy_remains_const:
  assumes "n \<le> i"
  shows "take n (strategy_progression \<sigma> p  $  i)  =  strategy_progression \<sigma> p  $  n"
  apply(rule sym,subst prefix_same_length_eq[symmetric])
  using assms plays_from_strategy_chain[OF assms] 
  by (auto intro!:prefix_takeI)

lemma infplays_augment_one[simp]:
  "strategy_progression \<sigma> (p @ [\<sigma> p]) = strategy_progression \<sigma> p"
proof(induct p)
  note defs = strategy_progression_def
  {
    case Nil
    then show ?case
      by (auto simp:defs iterates.code[of _ "[\<sigma> []]"])
  next
    case (Cons a p)
    then show ?case
      by (auto simp:defs iterates.code[of _ "a # p @ [\<sigma> (a # p)]"] lappend_llist_of_LCons)
  }
qed

lemma infplays_augment_many[simp]:
  "strategy_progression \<sigma> ((augment_list \<sigma> ^^ n) p) = strategy_progression \<sigma> p"
by(induct n,auto)

lemma infplays_augment_one_joint[simp]:
  "even (length p) \<Longrightarrow> strategy_progression (joint_strategy \<sigma>\<^sub>e \<sigma>\<^sub>o) (augment_list \<sigma>\<^sub>e p)
                     = strategy_progression (joint_strategy \<sigma>\<^sub>e \<sigma>\<^sub>o) p"
  "odd (length p)  \<Longrightarrow> strategy_progression (joint_strategy \<sigma>\<^sub>e \<sigma>\<^sub>o) (augment_list \<sigma>\<^sub>o p)
                     = strategy_progression (joint_strategy \<sigma>\<^sub>e \<sigma>\<^sub>o) p"
using infplays_augment_one[of "joint_strategy \<sigma>\<^sub>e \<sigma>\<^sub>o" p]
unfolding joint_strategy_def by auto

text \<open>Following two different strategies from a single position will lead to the same plays
      if the strategies agree on moves played after that position.
      This lemma allows us to ignore the behavior of strategies for moves that are already played. \<close>
lemma infplays_eq:
  assumes "\<And> p'. prefix p p' \<Longrightarrow> augment_list s1 p' = augment_list s2 p'"
  shows "strategy_progression s1 p = strategy_progression s2 p"
proof -
  from assms[of p] have [intro]:"s1 p = s2 p" by auto
  have "(augment_list s1 ^^ n) (augment_list s1 p) =
          (augment_list s2 ^^ n) (augment_list s2 p)" for n
    proof(induct n)
    case (Suc n)
    with assms[OF prefix_order.order.trans[OF _ prefix_augment]]
    show ?case by (auto)
  qed auto
  hence "strategy_progression s1 p $ n = strategy_progression s2 p $ n"
    for n (* different n *) unfolding strategy_progression_def lnth_lappend by auto
  thus ?thesis by(intro coinductive_eq_I,auto)
qed


context GSgame
begin

text \<open>By looking at the last elements of the infinite progression,
      we can get a single sequence, which we trim down to the right length.
      Since it has the right length, this always forms a play.
      We therefore name this the 'induced play'. \<close>

definition induced_play where
  "induced_play \<sigma> \<equiv> ltake (2*N) o lmap last o ltl o strategy_progression \<sigma>"

lemma induced_play_infinite_le[simp]:
  "enat x < llength (strategy_progression \<sigma> p)"
  "enat x < llength (lmap f (strategy_progression \<sigma> p))"
  "enat x < llength (ltake (2*N) (lmap f (strategy_progression \<sigma> p))) \<longleftrightarrow> x < 2*N"
using induced_play_infinite by auto

lemma induced_play_is_lprefix:
  assumes "position p"
  shows "lprefix (llist_of p) (induced_play \<sigma> p)"
proof -
  have l:"llength (llist_of p) \<le> 2 * N" using assms unfolding position_def by auto
  have "lprefix (llist_of p) (lmap last (ltl (llist_of (prefixes p))))" by auto
  hence "lprefix (llist_of p) ((lmap last o ltl o strategy_progression \<sigma>) p)"
    unfolding strategy_progression_def by(auto simp add: lmap_lappend_distrib lprefix_lappend)
  thus ?thesis unfolding induced_play_def o_def
    using lprefix_ltakeI[OF _ l] by blast
qed

lemma length_induced_play[simp]:
  "llength (induced_play s p) = 2 * N"
  unfolding induced_play_def by auto

lemma induced_play_lprefix_non_positions: (* 'opposite' of induced_play_is_lprefix *)
  assumes "length (p::'a list) \<ge> 2 * N"
  shows "induced_play \<sigma> p = ltake (2 * N) (llist_of p)"
proof(cases "N")
  case (enat nat)
  let ?p = "take (2 * nat) p"
  from assms have [intro]:"2 * N \<le> enat (length p)" by auto
  have [intro]:"2 * N \<le> enat (min (length p) (2 * nat))" unfolding enat
    by (metis assms enat min.orderI min_def numeral_eq_enat times_enat_simps(1))
  have [intro]:"enat (min (length p) (2 * nat)) = 2 * N"
    by (metis (mono_tags, lifting) assms enat min.absorb2 min_enat_simps(1)
        numeral_eq_enat times_enat_simps(1))
  have n:"2 * N \<le> llength (llist_of p)" "2 * N \<le> llength (llist_of (take (2 * nat) p))" by auto
  have pp:"position ?p"
    apply(subst position_def) (* for some reason 'unfolding' does not work here, tested in Isabelle 2021 *)
    by (metis (no_types, lifting) assms dual_order.order_iff_strict enat llength_llist_of
               llength_ltake' ltake_llist_of numeral_eq_enat take_all times_enat_simps(1))
  have lp:"lprefix (llist_of ?p) (induced_play \<sigma> ?p)" by(rule induced_play_is_lprefix[OF pp])
  (* this would make a great separate lemma, but we have a conversion between N and its nat
     to make that more involved *)
  have "ltake (2 * N) (llist_of p) = ltake (2 * N) (llist_of (take (2 * nat) p))"
    unfolding ltake_llist_of[symmetric] enat ltake_ltake numeral_eq_enat by auto
  hence eq:"induced_play \<sigma> p = induced_play \<sigma> ?p"
    unfolding induced_play_def strategy_progression_def
    by(auto simp add: lmap_lappend_distrib n[THEN ltake_lappend1])
  have "llist_of (take (2 * nat) p) = induced_play \<sigma> p"
    by(rule lprefix_llength_eq_imp_eq[OF lp[folded eq]],auto)
  then show ?thesis
     unfolding enat ltake_llist_of[symmetric] (* simp applies this one in the wrong direction *)
               numeral_eq_enat times_enat_simps(1) by metis
next
  case infinity
  hence "2 * N = \<infinity>" by (simp add: imult_is_infinity)
  then show ?thesis using assms by auto
qed

lemma infplays_augment_many_lprefix[simp]:
  shows "lprefix (llist_of ((augment_list \<sigma> ^^ n) p)) (induced_play \<sigma> p)
        = position ((augment_list \<sigma> ^^ n) p)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  from lprefix_llength_le[OF this] show ?rhs unfolding induced_play_def
    by (auto simp:position_def length_augment_list) next
  assume assm:?rhs
  from induced_play_is_lprefix[OF this, of "\<sigma>"]
  show ?lhs unfolding induced_play_def by simp
qed

subsection \<open> Winning strategies \<close>

text \<open> A strategy is winning (in position p) if, no matter the moves by the other player,
       it leads to a sequence in the winning set. \<close>
definition strategy_winning_by_Even where
  "strategy_winning_by_Even \<sigma>\<^sub>e p \<equiv> (\<forall> \<sigma>\<^sub>o. induced_play (joint_strategy \<sigma>\<^sub>e \<sigma>\<^sub>o) p \<in> A)"
definition strategy_winning_by_Odd where
  "strategy_winning_by_Odd \<sigma>\<^sub>o p \<equiv> (\<forall> \<sigma>\<^sub>e. induced_play (joint_strategy \<sigma>\<^sub>e \<sigma>\<^sub>o) p \<notin> A)"

text \<open> It immediately follows that not both players can have a winning strategy. \<close>
lemma at_most_one_player_winning:
shows "\<not> (\<exists> \<sigma>\<^sub>e. strategy_winning_by_Even \<sigma>\<^sub>e p) \<or> \<not> (\<exists> \<sigma>\<^sub>o. strategy_winning_by_Odd \<sigma>\<^sub>o p)"
  unfolding strategy_winning_by_Even_def strategy_winning_by_Odd_def by auto

text \<open> If a player whose turn it is not makes any move, winning strategies remain winning.
       All of the following proofs are duplicated for Even and Odd,
       as the game is entirely symmetrical. These 'dual' theorems can be obtained
       by considering a game in which an additional first and final move are played yet ignored,
       but it is quite convenient to have both theorems at hand regardless, and the proofs are
       quite small, so we accept the code duplication. \<close>

lemma any_moves_remain_winning_Even:
  assumes "odd (length p)" "strategy_winning_by_Even \<sigma> p"
  shows "strategy_winning_by_Even \<sigma> (p @ [m])"
unfolding strategy_winning_by_Even_def proof
  fix \<sigma>\<^sub>o
  let ?s = "\<sigma>\<^sub>o(p:=m)"
  have prfx:"prefix (p @ [m]) p' \<Longrightarrow>
             p' @ [joint_strategy \<sigma> \<sigma>\<^sub>o p'] = p' @ [joint_strategy \<sigma> ?s p']"
    for p' by (auto simp: joint_strategy_def)
  from assms(2)[unfolded strategy_winning_by_Even_def,rule_format,of ?s]
       infplays_augment_one_joint(2)[OF assms(1)]
  have "induced_play (joint_strategy \<sigma> ?s) (augment_list ?s p) \<in> A"
    by (metis (mono_tags, lifting) induced_play_def comp_apply)
  thus "induced_play (joint_strategy \<sigma> \<sigma>\<^sub>o) (p @ [m]) \<in> A"
    unfolding induced_play_def o_def
    using infplays_eq[OF prfx] by auto
qed

lemma any_moves_remain_winning_Odd:
  assumes "even (length p)" "strategy_winning_by_Odd \<sigma> p"
  shows "strategy_winning_by_Odd \<sigma> (p @ [m])"
unfolding strategy_winning_by_Odd_def proof
  fix \<sigma>\<^sub>e
  let ?s = "\<sigma>\<^sub>e(p:=m)"
  have prfx:"prefix (p @ [m]) p' \<Longrightarrow>
             p' @ [joint_strategy \<sigma>\<^sub>e \<sigma> p'] = p' @ [joint_strategy ?s \<sigma> p']"
    for p' by (auto simp:joint_strategy_def)
  from assms(2)[unfolded strategy_winning_by_Odd_def,rule_format,of ?s]
       infplays_augment_one_joint(1)[OF assms(1)]
  have "induced_play (joint_strategy ?s \<sigma>) (augment_list ?s p) \<notin> A"
    by (metis (mono_tags, lifting) induced_play_def comp_apply)
  thus "induced_play (joint_strategy \<sigma>\<^sub>e \<sigma>) (p @ [m]) \<notin> A"
    unfolding induced_play_def o_def
    using infplays_eq[OF prfx] by auto
qed

text \<open> If a player does not have a winning strategy,
       a move by that player will not give it one. \<close>

lemma non_winning_moves_remains_non_winning_Even:
  assumes "even (length p)" "\<forall> \<sigma>. \<not> strategy_winning_by_Even \<sigma> p"
  shows "\<not> strategy_winning_by_Even \<sigma> (p @ [m])"
proof(rule contrapos_nn[of "\<exists> \<sigma>. strategy_winning_by_Even \<sigma> p"])
  assume a:"strategy_winning_by_Even \<sigma> (p @ [m])"
  let ?s = "\<sigma>(p:=m)"
  have prfx:"prefix (p @ [m]) p' \<Longrightarrow>
             p' @ [joint_strategy \<sigma> \<sigma>\<^sub>o p'] = p' @ [joint_strategy ?s \<sigma>\<^sub>o p']"
    for p' \<sigma>\<^sub>o by (auto simp:joint_strategy_def)
  from a infplays_eq[OF prfx]
  have "strategy_winning_by_Even ?s (p @ [m])"
    unfolding strategy_winning_by_Even_def induced_play_def by simp
  hence "strategy_winning_by_Even ?s p" 
    using infplays_augment_one_joint(1)[OF assms(1)] 
    unfolding strategy_winning_by_Even_def induced_play_def o_def
    by (metis fun_upd_same)
  thus "\<exists>\<sigma>. strategy_winning_by_Even \<sigma> p" by blast next
  from assms(2) show "\<not> (\<exists> \<sigma>. strategy_winning_by_Even \<sigma> p)" by meson
qed

lemma non_winning_moves_remains_non_winning_Odd:
  assumes "odd (length p)" "\<forall> \<sigma>. \<not> strategy_winning_by_Odd \<sigma> p"
  shows "\<not> strategy_winning_by_Odd \<sigma> (p @ [m])"
proof(rule contrapos_nn[of "\<exists> \<sigma>. strategy_winning_by_Odd \<sigma> p"])
  assume a:"strategy_winning_by_Odd \<sigma> (p @ [m])"
  let ?s = "\<sigma>(p:=m)"
  have prfx:"prefix (p @ [m]) p' \<Longrightarrow>
             p' @ [joint_strategy \<sigma>\<^sub>e \<sigma> p'] = p' @ [joint_strategy \<sigma>\<^sub>e ?s p']"
    for p' \<sigma>\<^sub>e by (auto simp:joint_strategy_def)
  from a infplays_eq[OF prfx]
  have "strategy_winning_by_Odd ?s (p @ [m])"
    unfolding strategy_winning_by_Odd_def induced_play_def by simp
  hence "strategy_winning_by_Odd ?s p" 
    using infplays_augment_one_joint(2)[OF assms(1)] 
    unfolding strategy_winning_by_Odd_def induced_play_def o_def
    by (metis fun_upd_same)
  thus "\<exists>\<sigma>. strategy_winning_by_Odd \<sigma> p" by blast next
  from assms(2) show "\<not> (\<exists> \<sigma>. strategy_winning_by_Odd \<sigma> p)" by meson
qed

text \<open> If a player whose turn it is makes a move according to its stragey,
       the new position will remain winning. \<close>

lemma winning_moves_remain_winning_Even:
  assumes "even (length p)" "strategy_winning_by_Even \<sigma> p"
  shows "strategy_winning_by_Even \<sigma> (p @ [\<sigma> p])"
using assms infplays_augment_one
unfolding induced_play_def strategy_winning_by_Even_def by auto

lemma winning_moves_remain_winning_Odd:
  assumes "odd (length p)" "strategy_winning_by_Odd \<sigma> p"
  shows "strategy_winning_by_Odd \<sigma> (p @ [\<sigma> p])"
using assms infplays_augment_one
unfolding induced_play_def strategy_winning_by_Odd_def by auto

text \<open> We speak of winning positions as those positions in which the player has a winning strategy.
       This is mainly for presentation purposes. \<close>

abbreviation winning_position_Even where
  "winning_position_Even p \<equiv> position p \<and> (\<exists> \<sigma>. strategy_winning_by_Even \<sigma> p)"
abbreviation winning_position_Odd where
  "winning_position_Odd p \<equiv> position p \<and> (\<exists> \<sigma>. strategy_winning_by_Odd \<sigma> p)"

lemma winning_position_can_remain_winning_Even:
  assumes "even (length p)" "\<forall> m. position (p @ [m])" "winning_position_Even p"
  shows "\<exists> m. winning_position_Even (p @ [m])"
using assms winning_moves_remain_winning_Even[OF assms(1)] by auto

lemma winning_position_can_remain_winning_Odd:
  assumes "odd (length p)" "\<forall> m. position (p @ [m])" "winning_position_Odd p"
  shows "\<exists> m. winning_position_Odd (p @ [m])"
using assms winning_moves_remain_winning_Odd[OF assms(1)] by auto

lemma winning_position_will_remain_winning_Even:
  assumes "odd (length p)" "position (p @ [m])" "winning_position_Even p"
  shows "winning_position_Even (p @ [m])"
using assms any_moves_remain_winning_Even[OF assms(1)] by auto

lemma winning_position_will_remain_winning_Odd:
  assumes "even (length p)" "position (p @ [m])" "winning_position_Odd p"
  shows "winning_position_Odd (p @ [m])"
using assms any_moves_remain_winning_Odd[OF assms(1)] by auto

lemma induced_play_eq:
assumes "\<forall> p'. prefix p p' \<longrightarrow> (augment_list s1) p' = (augment_list s2) p'"
shows "induced_play s1 p = induced_play s2 p"
unfolding induced_play_def by (auto simp:infplays_eq[OF assms[rule_format]])

end

end