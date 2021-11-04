section\<open>An Observationally Equivalent Model\<close>
text\<open>This theory defines a second formalisation of the drinks machine example which produces
identical output to the first model. This property is called \emph{observational equivalence} and is
discussed in more detail in \cite{foster2018}.\<close>
theory Drinks_Machine_2
  imports Drinks_Machine
begin

(* Only imports Drinks_Machine_LTL so I can easily open all three at once for testing *)

definition vend_nothing :: "transition" where
"vend_nothing \<equiv> \<lparr>
        Label = (STR ''vend''),
        Arity = 0,
        Guards = [],
        Outputs =  [],
        Updates = [(1, V (R 1)), (2, V (R 2))]
      \<rparr>"

lemmas transitions = Drinks_Machine.transitions vend_nothing_def

definition drinks2 :: transition_matrix where
"drinks2 = {|
              ((0,1), select),
              ((1,1), vend_nothing),
              ((1,2), coin),
              ((2,2), coin),
              ((2,2), vend_fail),
              ((2,3), vend)
         |}"

lemma possible_steps_0:
  "length i = 1 \<Longrightarrow>
   possible_steps drinks2 0 r ((STR ''select'')) i = {|(1, select)|}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma possible_steps_1:
  "length i = 1 \<Longrightarrow>
   possible_steps drinks2 1 r ((STR ''coin'')) i = {|(2, coin)|}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma possible_steps_2_coin:
  "length i = 1 \<Longrightarrow>
   possible_steps drinks2 2 r ((STR ''coin'')) i = {|(2, coin)|}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma possible_steps_2_vend:
  "r $ 2 = Some (Num n) \<Longrightarrow>
   n \<ge> 100 \<Longrightarrow>
   possible_steps drinks2 2 r ((STR ''vend'')) [] = {|(3, vend)|}"
  apply (simp add: possible_steps_singleton drinks2_def)
  apply safe
  by (simp_all add: transitions apply_guards_def value_gt_def join_ir_def connectives)

lemma recognises_first_select:
  "recognises_execution drinks 0 r ((aa, b) # as) \<Longrightarrow> aa = STR ''select'' \<and> length b = 1"
  using recognises_must_be_possible_step[of drinks 0 r "(aa, b)" as]
  apply simp
  apply clarify
  by (metis first_step_select recognises_possible_steps_not_empty drinks_0_rejects fst_conv snd_conv)

lemma drinks2_vend_insufficient:
  "possible_steps drinks2 1 r ((STR ''vend'')) [] = {|(1, vend_nothing)|}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma drinks2_vend_insufficient2:
  "r $ 2 = Some (Num x1) \<Longrightarrow>
   x1 < 100 \<Longrightarrow>
   possible_steps drinks2 2 r ((STR ''vend'')) [] = {|(2, vend_fail)|}"
  apply (simp add: possible_steps_singleton drinks2_def)
  apply safe
  by (simp_all add: transitions apply_guards_def value_gt_def join_ir_def connectives)

lemma drinks2_vend_sufficient: "r $ 2 = Some (Num x1) \<Longrightarrow>
                \<not> x1 < 100 \<Longrightarrow>
                possible_steps drinks2 2 r ((STR ''vend'')) [] = {|(3, vend)|}"
  apply (simp add: possible_steps_singleton drinks2_def)
  apply safe
  by (simp_all add: transitions apply_guards_def value_gt_def join_ir_def connectives)

lemma recognises_1_2: "recognises_execution drinks 1 r t \<longrightarrow> recognises_execution drinks2 2 r t"
proof(induct t arbitrary: r)
  case (Cons a as)
  then show ?case
    apply (cases a)
    apply (simp add: recognises_step_equiv)
    apply (case_tac "a=(STR ''vend'', [])")
     apply (case_tac "\<exists>n. r$2 = Some (Num n)")
      apply clarify
      apply (case_tac "n < 100")
       apply (simp add: drinks_vend_insufficient drinks2_vend_insufficient2)
      apply (simp add: drinks_vend_sufficient drinks2_vend_sufficient)
      apply (metis recognises_prim recognises_prim.elims(3) drinks_rejects_future)
    using drinks_vend_invalid apply blast
    apply (case_tac "\<exists>i. a=(STR ''coin'', [i])")
     apply clarify
     apply (simp add: possible_steps_1_coin possible_steps_2_coin)
    by (metis recognises_execution.simps drinks_1_rejects_trace)
qed auto

lemma drinks_reject_0_2:
  "\<nexists>i. a = (STR ''select'', [i]) \<Longrightarrow>
   possible_steps drinks 0 r (fst a) (snd a) = {||}"
  apply (rule drinks_0_rejects)
  by (cases a, case_tac "snd a", auto)

lemma purchase_coke:
  "observe_execution drinks2 0 <> [((STR ''select''), [Str ''coke'']), ((STR ''coin''), [Num 50]), ((STR ''coin''), [Num 50]), ((STR ''vend''), [])] =
                       [[], [Some (Num 50)], [Some (Num 100)], [Some (Str ''coke'')]]"
  by (simp add: possible_steps_0 select_def apply_updates_def
                   possible_steps_1 coin_def apply_outputs finfun_update_twist
                   possible_steps_2_coin possible_steps_2_vend vend_def)

lemma drinks2_0_invalid:
  "\<not> (aa = (STR ''select'') \<and> length (b) = 1) \<Longrightarrow>
    (possible_steps drinks2 0 <> aa b) = {||}"
  apply (simp add: drinks2_def possible_steps_def transitions)
  by force

lemma drinks2_vend_r2_none:
  "r $ 2 = None \<Longrightarrow> possible_steps drinks2 2 r ((STR ''vend'')) [] = {||}"
  apply (simp add: possible_steps_empty drinks2_def can_take_transition_def can_take_def transitions)
  by (simp add: value_gt_def)

lemma drinks2_end: "possible_steps drinks2 3 r a b = {||}"
  apply (simp add: possible_steps_def drinks2_def transitions)
  by force

lemma drinks2_vend_r2_String: "r $ 2 = Some (value.Str x2) \<Longrightarrow>
                possible_steps drinks2 2 r ((STR ''vend'')) [] = {||}"
  apply (simp add: possible_steps_empty drinks2_def)
  apply safe
  by (simp_all add: transitions can_take_transition_def can_take_def value_gt_def)

lemma drinks2_2_invalid:
  "fst a = (STR ''coin'') \<longrightarrow> length (snd a) \<noteq> 1 \<Longrightarrow>
          a \<noteq> ((STR ''vend''), []) \<Longrightarrow>
          possible_steps drinks2 2 r (fst a) (snd a) = {||}"
  apply (simp add: possible_steps_empty drinks2_def transitions can_take_transition_def can_take_def)
  by (metis prod.collapse)

lemma drinks2_1_invalid:
  "\<not>(a = (STR ''coin'') \<and> length b = 1) \<Longrightarrow>
      \<not>(a = (STR ''vend'') \<and> b = []) \<Longrightarrow>
    possible_steps drinks2 1 r a b = {||}"
  apply (simp add: possible_steps_empty drinks2_def)
  apply safe
  by (simp_all add: transitions can_take_transition_def can_take_def value_gt_def)

lemma drinks2_vend_invalid:
  "\<nexists>n. r $ 2 = Some (Num n) \<Longrightarrow>
   possible_steps drinks2 2 r (STR ''vend'') [] = {||}"
  apply (simp add: possible_steps_empty drinks2_def)
  apply safe
  by (simp_all add: transitions can_take_transition_def can_take_def value_gt_def MaybeBoolInt_not_num_1)

lemma equiv_1_2: "executionally_equivalent drinks 1 r drinks2 2 r x"
proof(induct x arbitrary: r)
  case (Cons a t)
  then show ?case
    apply (cases a, clarsimp)
    apply (simp add: executionally_equivalent_step)
    apply (case_tac "fst a = STR ''coin'' \<and> length (snd a) = 1")
     apply (simp add: Drinks_Machine.possible_steps_1_coin possible_steps_2_coin)
    apply (case_tac "a = (STR ''vend'', [])")
     defer using drinks2_2_invalid drinks_no_possible_steps_1 apply auto[1]
    apply (case_tac "\<exists>n. r $ 2 = Some (Num n)")
     defer using drinks_vend_invalid drinks2_vend_invalid apply simp
    apply clarify
    subgoal for aa b n
      apply (case_tac "n < 100")
       apply (simp add: Drinks_Machine.drinks_vend_insufficient drinks2_vend_insufficient2)
      apply (simp add: Drinks_Machine.drinks_vend_sufficient drinks2_vend_sufficient)
      apply (induct t)
       apply simp
      subgoal for aa t apply (case_tac aa, clarsimp)
        by (simp add: executionally_equivalent_step drinks_end drinks2_end)
      done
    done
qed auto

lemma equiv_1_1: "r$2 = Some (Num 0) \<Longrightarrow> executionally_equivalent drinks 1 r drinks2 1 r x"
proof(induct x)
  case (Cons a t)
  then show ?case
    apply (cases a, clarsimp)
    subgoal for aa b
      apply (simp add: executionally_equivalent_step)
      apply (case_tac "aa = STR ''coin'' \<and> length b = 1")
       apply (simp add: possible_steps_1_coin possible_steps_1 equiv_1_2)
      apply (case_tac "a = (STR ''vend'', [])")
       apply clarsimp
       apply (simp add: drinks_vend_insufficient drinks2_vend_insufficient)
       apply (simp add: vend_fail_def vend_nothing_def apply_updates_def)
       apply (metis finfun_upd_triv)
      by (simp add: drinks2_1_invalid drinks_no_possible_steps_1)
    done
qed auto

(* Corresponds to Example 3 in Foster et. al. *)
lemma executional_equivalence: "executionally_equivalent drinks 0 <> drinks2 0 <> t"
proof(induct t)
  case (Cons a t)
  then show ?case
    apply (cases a, clarify)
    subgoal for aa b
      apply (simp add: executionally_equivalent_step)
      apply (case_tac "aa = STR ''select'' \<and> length b = 1")
       apply (simp add: Drinks_Machine.possible_steps_0 possible_steps_0)
       apply (simp add: apply_updates_def select_def equiv_1_1)
      by (simp add: drinks2_0_invalid possible_steps_0_invalid)
    done
qed auto

lemma observational_equivalence: "trace_equivalent drinks drinks2"
  by (simp add: executional_equivalence executionally_equivalent_trace_equivalent)

end
