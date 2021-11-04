chapter\<open>Examples\<close>
text\<open>In this chapter, we provide some examples of EFSMs and proofs over them. We first present a
formalisation of a simple drinks machine. Next, we prove observational equivalence of an alternative
model. Finally, we prove some temporal properties of the first example.\<close>

section\<open>Drinks Machine\<close>
text\<open>This theory formalises a simple drinks machine. The \emph{select} operation takes one
argument - the desired beverage. The \emph{coin} operation also takes one parameter representing
the value of the coin. The \emph{vend} operation has two flavours - one which dispenses the drink if
the customer has inserted enough money, and one which dispenses nothing if the user has not inserted
sufficient funds.

We first define a datatype \emph{statemane} which corresponds to $S$ in the formal definition.
Note that, while statename has four elements, the drinks machine presented here only requires three
states. The fourth element is included here so that the \emph{statename} datatype may be used in
the next example.\<close>
theory Drinks_Machine
  imports "Extended_Finite_State_Machines.EFSM"
begin

text_raw\<open>\snip{selectdef}{1}{2}{%\<close>
definition select :: "transition" where
"select \<equiv> \<lparr>
        Label = STR ''select'',
        Arity = 1,
        Guards = [],
        Outputs = [],
        Updates = [
                    (1, V (I 0)),
                    (2, L (Num 0))
                  ]
      \<rparr>"
text_raw\<open>}%endsnip\<close>

text_raw\<open>\snip{coindef}{1}{2}{%\<close>
definition coin :: "transition" where
"coin \<equiv> \<lparr>
        Label = STR ''coin'',
        Arity = 1,
        Guards = [],
        Outputs = [Plus (V (R 2)) (V (I 0))],
        Updates = [
                    (1, V (R 1)),
                    (2, Plus (V (R 2)) (V (I 0)))
                  ]
      \<rparr>"
text_raw\<open>}%endsnip\<close>

text_raw\<open>\snip{venddef}{1}{2}{%\<close>
definition vend:: "transition" where
"vend\<equiv> \<lparr>
        Label = STR ''vend'',
        Arity = 0,
        Guards = [(Ge (V (R 2)) (L (Num 100)))],
        Outputs =  [(V (R 1))],
        Updates = [(1, V (R 1)), (2, V (R 2))]
      \<rparr>"
text_raw\<open>}%endsnip\<close>

text_raw\<open>\snip{vendfaildef}{1}{2}{%\<close>
definition vend_fail :: "transition" where
"vend_fail \<equiv> \<lparr>
        Label = STR ''vend'',
        Arity = 0,
        Guards = [(Lt (V (R 2)) (L (Num 100)))],
        Outputs =  [],
        Updates = [(1, V (R 1)), (2, V (R 2))]
      \<rparr>"
text_raw\<open>}%endsnip\<close>

text_raw\<open>\snip{drinksdef}{1}{2}{%\<close>
definition drinks :: "transition_matrix" where
"drinks \<equiv> {|
          ((0,1), select),
          ((1,1), coin),
          ((1,1), vend_fail),
          ((1,2), vend)
         |}"
text_raw\<open>}%endsnip\<close>

lemmas transitions = select_def coin_def vend_def vend_fail_def

lemma apply_updates_vend: "apply_updates (Updates vend) (join_ir [] r) r = r"
  by (simp add: vend_def apply_updates_def)

lemma drinks_states: "S drinks = {|0, 1, 2|}"
  apply (simp add: S_def drinks_def)
  by auto

lemma possible_steps_0:
  "length i = 1 \<Longrightarrow>
   possible_steps drinks 0 r (STR ''select'') i = {|(1, select)|}"
  apply (simp add: possible_steps_singleton drinks_def)
  apply safe
  by (simp_all add: transitions apply_guards_def)

lemma first_step_select:
  "(s', t) |\<in>| possible_steps drinks 0 r aa b \<Longrightarrow> s' = 1 \<and> t = select"
  apply (simp add: possible_steps_def fimage_def ffilter_def fmember_def Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: transitions)

lemma drinks_vend_insufficient:
  "r $ 2 = Some (Num x1) \<Longrightarrow>
   x1 < 100 \<Longrightarrow>
   possible_steps drinks 1 r (STR ''vend'') [] = {|(1, vend_fail)|}"
  apply (simp add: possible_steps_singleton drinks_def)
  apply safe
  by (simp_all add: transitions apply_guards_def value_gt_def join_ir_def connectives)

lemma drinks_vend_invalid:
  "\<nexists>n. r $ 2 = Some (Num n) \<Longrightarrow>
   possible_steps drinks 1 r (STR ''vend'') [] = {||}"
  apply (simp add: possible_steps_empty drinks_def can_take_transition_def can_take_def transitions)
  by (simp add: MaybeBoolInt_not_num_1 value_gt_def)

lemma possible_steps_1_coin:
  "length i = 1 \<Longrightarrow> possible_steps drinks 1 r (STR ''coin'') i = {|(1, coin)|}"
  apply (simp add: possible_steps_singleton drinks_def)
  apply safe
  by (simp_all add: transitions)

lemma possible_steps_2_vend:
  "\<exists>n. r $ 2 = Some (Num n) \<and> n \<ge> 100 \<Longrightarrow>
   possible_steps drinks 1 r (STR ''vend'') [] = {|(2, vend)|}"
  apply (simp add: possible_steps_singleton drinks_def)
  apply safe
  by (simp_all add: transitions apply_guards_def value_gt_def join_ir_def connectives)

lemma recognises_from_2:
  "recognises_execution drinks 1 <1 $:= d, 2 $:= Some (Num 100)> [(STR ''vend'', [])]"
  apply (rule recognises_execution.step)
  apply (rule_tac x="(2, vend)" in fBexI)
   apply simp
  by (simp add: possible_steps_2_vend)

lemma recognises_from_1a:
  "recognises_execution drinks 1 <1 $:= d, 2 $:= Some (Num 50)> [(STR ''coin'', [Num 50]), (STR ''vend'', [])]"
  apply (rule recognises_execution.step)
  apply (rule_tac x="(1, coin)" in fBexI)
   apply (simp add: apply_updates_def coin_def finfun_update_twist value_plus_def recognises_from_2)
  by (simp add: possible_steps_1_coin)

lemma recognises_from_1: "recognises_execution drinks 1 <2 $:= Some (Num 0), 1 $:= Some d>
     [(STR ''coin'', [Num 50]), (STR ''coin'', [Num 50]), (STR ''vend'', [])]"
  apply (rule recognises_execution.step)
  apply (rule_tac x="(1, coin)" in fBexI)
   apply (simp add: apply_updates_def coin_def value_plus_def finfun_update_twist recognises_from_1a)
  by (simp add: possible_steps_1_coin)

lemma purchase_coke:
  "observe_execution drinks 0 <> [(STR ''select'', [Str ''coke'']), (STR ''coin'', [Num 50]), (STR ''coin'', [Num 50]), (STR ''vend'', [])] =
                       [[], [Some (Num 50)], [Some (Num 100)], [Some (Str ''coke'')]]"
  by (simp add: possible_steps_0 possible_steps_1_coin possible_steps_2_vend transitions
                   apply_outputs_def apply_updates_def value_plus_def)

lemma rejects_input:
  "l \<noteq> STR ''coin'' \<Longrightarrow>
   l \<noteq> STR ''vend'' \<Longrightarrow>
   \<not> recognises_execution drinks 1 d' [(l, i)]"
  apply (rule no_possible_steps_rejects)
  by (simp add: possible_steps_empty drinks_def can_take_transition_def can_take_def transitions)

lemma rejects_recognises_prefix: "l \<noteq> STR ''coin'' \<Longrightarrow>
   l \<noteq> STR ''vend'' \<Longrightarrow>
   \<not> (recognises drinks [(STR ''select'', [Str ''coke'']), (l, i)])"
  apply (rule trace_reject_later)
  apply (simp add: possible_steps_0 select_def join_ir_def input2state_def)
  using rejects_input by blast

lemma rejects_termination:
  "observe_execution drinks 0 <> [(STR ''select'', [Str ''coke'']), (STR ''rejects'', [Num 50]), (STR ''coin'', [Num 50])] = [[]]"
  apply (rule observe_execution_step)
   apply (simp add: step_def possible_steps_0 select_def)
  apply (rule observe_execution_no_possible_step)
  by (simp add: possible_steps_empty drinks_def can_take_transition_def can_take_def transitions)

(* Part of Example 2 in Foster et. al. *)
lemma r2_0_vend:
  "can_take_transition vend i r \<Longrightarrow>
   \<exists>n. r $ 2 = Some (Num n) \<and> n \<ge> 100" (* You can't take vendimmediately after taking select *)
  apply (simp add: can_take_transition_def can_take_def vend_def apply_guards_def maybe_negate_true maybe_or_false connectives value_gt_def)
  using MaybeBoolInt.elims by force

lemma drinks_vend_sufficient: "r $ 2 = Some (Num x1) \<Longrightarrow>
                x1 \<ge> 100 \<Longrightarrow>
                possible_steps drinks 1 r (STR ''vend'') [] = {|(2, vend)|}"
  using possible_steps_2_vend by blast

lemma drinks_end: "possible_steps drinks 2 r a b = {||}"
  apply (simp add: possible_steps_def drinks_def transitions)
  by force

lemma drinks_vend_r2_String:
  "r $ 2 = Some (value.Str x2) \<Longrightarrow>
   possible_steps drinks 1 r (STR ''vend'') [] = {||}"
  apply (simp add: possible_steps_empty drinks_def can_take_transition_def can_take_def transitions)
  by (simp add: value_gt_def)

lemma drinks_vend_r2_rejects:
  "\<nexists>n. r $ 2 = Some (Num n) \<Longrightarrow> step drinks 1 r (STR ''vend'') [] = None"
  apply (rule no_possible_steps_1)
  apply (simp add: possible_steps_empty drinks_def can_take_transition_def can_take_def transitions)
  by (simp add: MaybeBoolInt_not_num_1 value_gt_def)

lemma drinks_0_rejects:
  "\<not> (fst a = STR ''select'' \<and> length (snd a) = 1) \<Longrightarrow>
    (possible_steps drinks 0 r (fst a) (snd a)) = {||}"
  apply (simp add: drinks_def possible_steps_def transitions)
  by force

lemma drinks_vend_empty: "(possible_steps drinks 0 <> (STR ''vend'') []) = {||}"
  using drinks_0_rejects
  by auto

lemma drinks_1_rejects:
  "fst a = STR ''coin'' \<longrightarrow> length (snd a) \<noteq> 1 \<Longrightarrow>
          a \<noteq> (STR ''vend'', []) \<Longrightarrow>
          possible_steps drinks 1 r (fst a) (snd a) = {||}"
  apply (simp add: possible_steps_empty drinks_def can_take_transition_def can_take_def transitions)
  by (metis prod.collapse)

lemma drinks_rejects_future: "\<not> recognises_execution drinks 2 d ((l, i)#t)"
  apply (rule no_possible_steps_rejects)
  by (simp add: possible_steps_empty drinks_def)

lemma drinks_1_rejects_trace:
  assumes not_vend: "e \<noteq> (STR ''vend'', [])"
      and not_coin: "\<nexists>i. e = (STR ''coin'', [i])"
  shows "\<not> recognises_execution drinks 1 r (e # es)"
proof-
  show ?thesis
    apply (cases e, simp)
    subgoal for a b
      apply (rule no_possible_steps_rejects)
      apply (simp add: possible_steps_empty drinks_def can_take_transition_def can_take_def transitions)
      apply (case_tac b)
      using not_vend apply simp
      using not_coin by auto
    done
qed

lemma rejects_state_step: "s > 1 \<Longrightarrow> step drinks s r l i = None"
  apply (rule no_possible_steps_1)
  by (simp add: possible_steps_empty drinks_def)

lemma invalid_other_states:
  "s > 1 \<Longrightarrow> \<not> recognises_execution drinks s r ((aa, b) # t)"
  apply (rule no_possible_steps_rejects)
  by (simp add: possible_steps_empty drinks_def)

lemma vend_ge_100:
  "possible_steps drinks 1 r l i = {|(2, vend)|} \<Longrightarrow>
   \<not>? value_gt (Some (Num 100)) (r $ 2) = trilean.true"
  apply (insert possible_steps_apply_guards[of drinks 1 r l i 2 vend])
  by (simp add: possible_steps_def apply_guards_def vend_def)

lemma drinks_no_possible_steps_1:
  assumes not_coin: "\<not> (a = STR ''coin'' \<and> length b = 1)"
      and not_vend: "\<not> (a = STR ''vend'' \<and> b = [])"
    shows "possible_steps drinks 1 r a b = {||}"
  using drinks_1_rejects not_coin not_vend by auto

lemma possible_steps_0_not_select: "a \<noteq> STR ''select'' \<Longrightarrow>
       possible_steps drinks 0 <> a b = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: select_def)

lemma possible_steps_select_wrong_arity: "a = STR ''select'' \<Longrightarrow>
       length b \<noteq> 1 \<Longrightarrow>
       possible_steps drinks 0 <> a b = {||}"
  apply (simp add: possible_steps_def ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def drinks_def)
  apply safe
  by (simp_all add: select_def)

lemma possible_steps_0_invalid:
  "\<not> (l = STR ''select'' \<and> length i = 1) \<Longrightarrow>
   possible_steps drinks 0 <> l i = {||}"
  using possible_steps_0_not_select possible_steps_select_wrong_arity by fastforce

end
