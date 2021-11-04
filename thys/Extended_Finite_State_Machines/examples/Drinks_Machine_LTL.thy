section\<open>Temporal Properties\<close>
text\<open>This theory presents some examples of temporal properties over the simple drinks machine.\<close>

theory Drinks_Machine_LTL
imports "Drinks_Machine" "Extended_Finite_State_Machines.EFSM_LTL"
begin

declare One_nat_def [simp del]

lemma P_ltl_step_0:
  assumes invalid: "P (None, [], <>)"
  assumes select: "l = STR ''select'' \<longrightarrow> P (Some 1, [], <1 $:= Some (hd i), 2 $:= Some (Num 0)>)"
  shows "P (ltl_step drinks (Some 0) <> (l, i))"
proof-
  have length_i: "\<exists>d. (l, i) = (STR ''select'', [d]) \<Longrightarrow> length i = 1"
    by (induct i, auto)
  have length_i_2: "\<forall>d. i \<noteq> [d] \<Longrightarrow> length i \<noteq> 1"
    by (induct i, auto)
  show ?thesis
    apply (case_tac "\<exists>d. (l, i) = (STR ''select'', [d])")
     apply (simp add: possible_steps_0 length_i select_def apply_updates_def)
    using select apply auto[1]
    by (simp add: possible_steps_0_invalid length_i_2 invalid)
qed

lemma P_ltl_step_1:
  assumes invalid: "P (None, [], r)"
  assumes coin: "l = STR ''coin'' \<longrightarrow> P (Some 1, [value_plus (r $ 2) (Some (hd i))], r(2 $:= value_plus (r $ 2) (Some (i ! 0))))"
  assumes vend_fail: "value_gt (Some (Num 100)) (r $ 2) = trilean.true \<longrightarrow> P (Some 1, [],r)"
  assumes vend: "\<not>? value_gt (Some (Num 100)) (r $ 2) = trilean.true \<longrightarrow> P (Some 2, [r$1], r)"
  shows "P (ltl_step drinks (Some 1) r (l, i))"
proof-
  have length_i: "\<And>s. \<exists>d. (l, i) = (s, [d]) \<Longrightarrow> length i = 1"
    by (induct i, auto)
  have length_i_2: "\<forall>d. i \<noteq> [d] \<Longrightarrow> length i \<noteq> 1"
    by (induct i, auto)
  show ?thesis
    apply (case_tac "\<exists>d. (l, i) = (STR ''coin'', [d])")
     apply (simp add: possible_steps_1_coin length_i coin_def apply_outputs_def apply_updates_def)
    using coin apply auto[1]
    apply (case_tac "(l, i) = (STR ''vend'', [])")
     apply (case_tac "\<exists>n. r $ 2 = Some (Num n)")
      apply clarsimp
    subgoal for n
      apply (case_tac "n \<ge> 100")
       apply (simp add: drinks_vend_sufficient vend_def apply_updates_def apply_outputs_def)
       apply (metis finfun_upd_triv possible_steps_2_vend vend vend_ge_100)
      apply (simp add: drinks_vend_insufficient vend_fail_def apply_updates_def apply_outputs_def)
      apply (metis MaybeBoolInt.simps(1) finfun_upd_triv not_less value_gt_def vend_fail)
      done
     apply (simp add: drinks_vend_invalid invalid)
    by (simp add: drinks_no_possible_steps_1 length_i_2 invalid)
qed

lemma LTL_r2_not_always_gt_100: "not (alw (check_exp (Gt (V (Rg 2)) (L (Num 100))))) (watch drinks i)"
  using value_gt_def by auto

lemma drinks_step_2_none: "ltl_step drinks (Some 2) r e = (None, [], r)"
  by (simp add: drinks_end ltl_step_none_2)

lemma one_before_two_2:
  "alw (\<lambda>x. statename (shd (stl x)) = Some 2 \<longrightarrow> statename (shd x) = Some 1) (make_full_observation drinks (Some 2) r [r $ 1] x2a)"
proof(coinduction)
  case alw
  then show ?case
    apply (simp add: drinks_step_2_none)
    by (metis (mono_tags, lifting) alw_mono nxt.simps once_none_nxt_always_none option.distinct(1))
qed

lemma one_before_two_aux:
  assumes "\<exists> p r i. j = nxt (make_full_observation drinks (Some 1) r p) i"
  shows "alw (\<lambda>x. nxt (state_eq (Some 2)) x \<longrightarrow> state_eq (Some 1) x) j"
  using assms apply(coinduct)
  apply simp
  apply clarify
  apply standard
   apply simp
  apply simp
  subgoal for r i
    apply (case_tac "shd (stl i)")
    apply (simp del: ltl_step.simps)
    apply (rule P_ltl_step_1)
       apply (rule disjI2)
       apply (rule alw_mono[of "nxt (state_eq None)"])
        apply (simp add: once_none_nxt_always_none)
       apply simp
      apply auto[1]
     apply auto[1]
    apply simp
    by (simp add: one_before_two_2)
  done

lemma LTL_nxt_2_means_vend:
  "alw (nxt (state_eq (Some 2)) impl (state_eq (Some 1))) (watch drinks i)"
proof(coinduction)
  case alw
  then show ?case
    apply (case_tac "shd i")
    apply (simp del: ltl_step.simps)
    apply (rule P_ltl_step_0)
     apply simp
     apply (rule disjI2)
     apply (rule alw_mono[of "nxt (state_eq None)"])
      apply (simp add: once_none_nxt_always_none)
    using one_before_two_aux by auto
qed

lemma costsMoney_aux:
  assumes "\<exists>p r i. j = (nxt (make_full_observation drinks (Some 1) r p) i)"
  shows "alw (\<lambda>xs. nxt (state_eq (Some 2)) xs \<longrightarrow> check_exp (Ge (V (Rg 2)) (L (Num 100))) xs) j"
  using assms apply coinduct
  apply clarsimp
  subgoal for r i
    apply (case_tac "shd (stl i)")
    apply (simp del: ltl_step.simps)
    apply (rule P_ltl_step_1)
       apply simp
       apply (rule disjI2)
       apply (rule alw_mono[of "nxt (state_eq None)"])
        apply (simp add: once_none_nxt_always_none)
       apply simp
      apply auto[1]
     apply auto[1]
    apply simp
    apply standard
    apply (rule disjI2)
    apply (rule alw_mono[of "nxt (state_eq None)"])
     apply (metis (no_types, lifting) drinks_step_2_none fst_conv make_full_observation.sel(2) nxt.simps nxt_alw once_none_always_none_aux)
    by simp
  done

(* costsMoney: THEOREM drinks |- G(X(cfstate=State_2) => gval(value_ge(r_2, Some(NUM(100))))); *)
lemma LTL_costsMoney:
  "(alw (nxt (state_eq (Some 2)) impl (check_exp (Ge (V (Rg 2)) (L (Num 100)))))) (watch drinks i)"
proof(coinduction)
  case alw
  then show ?case
    apply (cases "shd i")
    subgoal for l ip
      apply (case_tac "l = STR ''select'' \<and> length ip = 1")
       defer
       apply (simp add: possible_steps_0_invalid)
       apply (rule disjI2)
       apply (rule alw_mono[of "nxt (state_eq None)"])
        apply (simp add: once_none_nxt_always_none)
       apply (simp add: )
      apply (simp add: possible_steps_0 select_def)
      apply (rule disjI2)
      apply (simp only: nxt.simps[symmetric])
      using costsMoney_aux by auto
    done
qed

lemma LTL_costsMoney_aux:
  "(alw (not (check_exp (Ge (V (Rg 2)) (L (Num 100)))) impl (not (nxt (state_eq (Some 2)))))) (watch drinks i)"
  by (metis (no_types, lifting) LTL_costsMoney alw_mono)

lemma implode_select: "String.implode ''select'' = STR ''select''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_coin: "String.implode ''coin'' = STR ''coin''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemma implode_vend: "String.implode ''vend'' = STR ''vend''"
  by (metis Literal.rep_eq String.implode_explode_eq zero_literal.rep_eq)

lemmas implode_labels = implode_select implode_coin implode_vend

lemma LTL_neverReachS2:"(((((action_eq (''select'', [Str ''coke''])))
                    aand
                    (nxt ((action_eq (''coin'', [Num 100])))))
                    aand
                    (nxt (nxt((label_eq ''vend'' aand (input_eq []))))))
                    impl
                    (nxt (nxt (nxt (state_eq (Some 2))))))
                    (watch drinks i)"
  apply (simp add: implode_labels)
  apply (cases i)
  apply clarify  
  apply simp
  apply (simp add: possible_steps_0 select_def)
  apply (case_tac "shd x2", clarify)
  apply (simp add: possible_steps_1_coin coin_def value_plus_def finfun_update_twist apply_updates_def)
  apply (case_tac "shd (stl x2)", clarify)
  by (simp add: drinks_vend_sufficient )

lemma ltl_step_not_select:
  "\<nexists>i. e = (STR ''select'', [i]) \<Longrightarrow>
   ltl_step drinks (Some 0) r e = (None, [], r)"
  apply (cases e, clarify)
  subgoal for a b
    apply (rule ltl_step_none)
    apply (simp add: possible_steps_empty drinks_def can_take_transition_def can_take_def select_def)
    by (cases e, case_tac b, auto)
  done

lemma ltl_step_select:
  "ltl_step drinks (Some 0) <> (STR ''select'', [i]) = (Some 1, [], <1 $:= Some i, 2 $:= Some (Num 0)>)"
  apply (rule  ltl_step_some[of _ _ _ _ _ _ select])
    apply (simp add: possible_steps_0)
   apply (simp add: select_def)
  by (simp add: select_def finfun_update_twist apply_updates_def)

lemma ltl_step_not_coin_or_vend:
  "\<nexists>i. e = (STR ''coin'', [i]) \<Longrightarrow>
    e \<noteq> (STR ''vend'', []) \<Longrightarrow>
    ltl_step drinks (Some 1) r e = (None, [], r)"
  apply (cases e)
  subgoal for a b
    apply (simp del: ltl_step.simps)
    apply (rule ltl_step_none)
    apply (simp add: possible_steps_empty drinks_def can_take_transition_def can_take_def transitions)
    by (case_tac e, case_tac b, auto)
  done

lemma ltl_step_coin:
  "\<exists>p r'. ltl_step drinks (Some 1) r (STR ''coin'', [i]) = (Some 1, p, r')"
  by (simp add: possible_steps_1_coin)

lemma alw_tl:
  "alw \<phi> (make_full_observation e (Some 0) <> [] xs) \<Longrightarrow>
    alw \<phi>
     (make_full_observation e (fst (ltl_step e (Some 0) <> (shd xs))) (snd (snd (ltl_step e (Some 0) <> (shd xs))))
       (fst (snd (ltl_step e (Some 0) <> (shd xs)))) (stl xs))"
  by auto

lemma stop_at_none:
  "alw (\<lambda>xs. output (shd (stl xs)) = [Some (EFSM.Str drink)] \<longrightarrow> check_exp (Ge (V (Rg 2)) (L (Num 100))) xs)
            (make_full_observation drinks None r p t)"
  apply (rule alw_mono[of "nxt (output_eq [])"])
   apply (simp add: no_output_none_nxt)
  by simp

lemma drink_costs_money_aux:
  assumes "\<exists>p r t. j = make_full_observation drinks (Some 1) r p t"
  shows "alw (\<lambda>xs. output (shd (stl xs)) = [Some (EFSM.Str drink)] \<longrightarrow> check_exp (Ge (V (Rg 2)) (L (Num 100))) xs) j"
  using assms apply coinduct
  apply clarsimp
  apply (case_tac "shd t")
  apply (simp del: ltl_step.simps)
  apply (rule P_ltl_step_1)
     apply simp
     apply (rule disjI2)
     apply (rule alw_mono[of "nxt (output_eq [])"])
      apply (simp add: no_output_none_nxt)
     apply simp
    apply (simp add: Str_def value_plus_never_string)
    apply auto[1]
   apply auto[1]
  apply simp
  apply standard
  apply (rule disjI2)
  apply (rule alw_mono[of "nxt (output_eq [])"])
   apply (simp add: drinks_step_2_none no_output_none_if_empty nxt_alw)
  by simp

lemma LTL_drinks_cost_money:
  "alw (nxt (output_eq [Some (Str drink)]) impl (check_exp (Ge (V (Rg 2)) (L (Num 100))))) (watch drinks t)"
proof(coinduction)
  case alw
  then show ?case
    apply (case_tac "shd t")
    apply (simp del: ltl_step.simps)
    apply (rule P_ltl_step_0)
     apply simp
     apply (rule disjI2)
     apply (rule alw_mono[of "nxt (output_eq [])"])
      apply (simp add: no_output_none_nxt)
     apply simp
    apply simp
    using drink_costs_money_aux
    apply simp
    by blast
qed

lemma steps_1_invalid:
      "\<nexists>i. (a, b) = (STR ''coin'', [i]) \<Longrightarrow>
       \<nexists>i. (a, b) = (STR ''vend'', []) \<Longrightarrow>
       possible_steps drinks 1 r a b = {||}"
  apply (simp add: possible_steps_empty drinks_def transitions can_take_transition_def can_take_def)
  by (induct b, auto)

lemma output_vend_aux:
  assumes "\<exists>p r t. j = make_full_observation drinks (Some 1) r p t"
  shows "alw (\<lambda>xs. label_eq ''vend'' xs \<and> output (shd (stl xs)) = [Some d] \<longrightarrow> check_exp (Ge (V (Rg 2)) (L (Num 100))) xs) j"
  using assms apply coinduct
  apply clarsimp
  subgoal for r t
    apply (case_tac "shd t")
    apply (simp add: implode_vend del: ltl_step.simps)
    apply (rule P_ltl_step_1)
       apply simp
       apply (rule disjI2)
       apply (rule alw_mono[of "nxt (output_eq [])"])
        apply (simp add: no_output_none_nxt)
       apply simp
      apply auto[1]
     apply auto[1]
    apply simp
    apply standard
    apply (rule disjI2)
    apply (rule alw_mono[of "nxt (output_eq [])"])
     apply (simp add: drinks_step_2_none no_output_none_if_empty nxt_alw)
    by simp
  done

text_raw\<open>\snip{outputVend}{1}{2}{%\<close>
lemma LTL_output_vend:
  "alw (((label_eq ''vend'') aand (nxt (output_eq [Some d]))) impl
         (check_exp (Ge (V (Rg 2)) (L (Num 100))))) (watch drinks t)"
text_raw\<open>}%endsnip\<close>
proof(coinduction)
  case alw
  then show ?case
    apply (simp add: implode_vend)
    apply (case_tac "shd t")
    apply (simp del: ltl_step.simps)
    apply (rule P_ltl_step_0)
     apply simp
    apply (rule disjI2)
     apply (rule alw_mono[of "nxt (output_eq [])"])
      apply (simp add: no_output_none_nxt)
     apply simp
    apply simp
    subgoal for a b
      using output_vend_aux[of "(make_full_observation drinks (Some 1)
              <1 $:= Some (hd b), 2 $:= Some (Num 0)> [] (stl t))" d]
      using implode_vend by auto
    done
qed

text_raw\<open>\snip{outputVendUnfolded}{1}{2}{%\<close>
lemma LTL_output_vend_unfolded:
  "alw (\<lambda>xs. (label (shd xs) = STR ''vend'' \<and>
             nxt (\<lambda>s. output (shd s) = [Some d]) xs) \<longrightarrow>
              \<not>? value_gt (Some (Num 100)) (datastate (shd xs) $ 2) = trilean.true)
     (watch drinks t)"
text_raw\<open>}%endsnip\<close>
  apply (insert LTL_output_vend[of d t])
  by (simp add: implode_vend)

end
