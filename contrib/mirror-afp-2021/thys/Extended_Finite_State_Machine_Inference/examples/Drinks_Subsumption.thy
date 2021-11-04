subsection\<open>Example\<close> 
text\<open>This theory shows how contexts can be used to prove transition subsumption.\<close>
theory Drinks_Subsumption
imports "Extended_Finite_State_Machine_Inference.Subsumption" "Extended_Finite_State_Machines.Drinks_Machine_2"
begin

lemma stop_at_3: "\<not>obtains 1 c drinks2 3 r t"
proof(induct t arbitrary: r)
  case Nil
  then show ?case
    by (simp add: obtains_base)
next
  case (Cons a t)
  then show ?case
    apply (case_tac a)
    apply (simp add: obtains_step)
    apply clarify
    apply (simp add: in_possible_steps[symmetric])
    by (simp add: drinks2_def)
qed

lemma no_1_2: "\<not>obtains 1 c drinks2 2 r t"
proof(induct t arbitrary: r)
  case Nil
  then show ?case
    by (simp add: obtains_base)
next
  case (Cons a t)
  then show ?case
    apply (case_tac a)
    apply (simp add: obtains_step)
    apply clarify
    apply (simp add: in_possible_steps[symmetric])
    apply (simp add: drinks2_def)
    apply clarsimp
    apply (simp add: drinks2_def[symmetric])
    apply (erule disjE)
     apply simp
    apply (erule disjE)
     apply simp
    by (simp add: stop_at_3)
qed

lemma no_change_1_1: "obtains 1 c drinks2 1 r t \<Longrightarrow> c = r"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: obtains_base)
next
  case (Cons a t)
  then show ?case
    apply (case_tac a)
    apply (simp add: obtains_step)
    apply clarify
    apply (simp add: in_possible_steps[symmetric])
    apply (simp add: drinks2_def)
    apply clarsimp
    apply (simp add: drinks2_def[symmetric])
    apply (erule disjE)
     apply (simp add: vend_nothing_def apply_updates_def)
    by (simp add: no_1_2)
qed

lemma obtains_1: "obtains 1 c drinks2 0 <> t \<Longrightarrow> c $ 2 = Some (Num 0)"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: obtains_base)
next
  case (Cons a t)
  then show ?case
    apply (case_tac a)
    apply (simp add: obtains_step)
    apply clarify
    apply (simp add: in_possible_steps[symmetric])
    apply (simp add: drinks2_def)
    apply (simp add: drinks2_def[symmetric])
    apply (simp add: select_def can_take apply_updates_def)
    using no_change_1_1 by fastforce
qed

lemma obtains_1_1_2:
  "obtains 1 c1 drinks2 1 r t \<Longrightarrow>
   obtains 1 c2 drinks 1 r t \<Longrightarrow>
   c1 = r \<and> c2 = r"
proof(induct t arbitrary: r)
  case Nil
  then show ?case
    by (simp add: obtains_base)
next
  case (Cons a t)
  then show ?case
    apply (case_tac a)
    apply (simp add: obtains_step)
    apply clarify
    apply (simp add: in_possible_steps[symmetric])
    apply (simp add: drinks2_def drinks_def)
    apply clarsimp
    apply (simp add: drinks2_def[symmetric] drinks_def[symmetric])
    apply safe
    using Cons.prems(1) no_change_1_1 apply blast
              apply (simp add: coin_def vend_nothing_def)
    using Cons.prems(1) no_change_1_1 apply blast
            apply (simp add: vend_fail_def vend_nothing_def apply_updates_def)
    using Cons.prems(1) no_change_1_1 apply blast
          apply (metis drinks_rejects_future numeral_eq_one_iff obtains.cases obtains_recognises semiring_norm(85))
    using no_1_2 apply blast
    using no_1_2 apply blast
    using Cons.prems(1) no_change_1_1 apply blast
    using no_1_2 apply blast
    using no_1_2 apply blast
    using no_1_2 by blast
qed

lemma obtains_1_c2:
  "obtains 1 c1 drinks2 0 <> t \<Longrightarrow> obtains 1 c2 drinks 0 <> t \<Longrightarrow> c2 $ 2 = Some (Num 0)"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: obtains_base)
next
  case (Cons a t)
  then show ?case
    apply (case_tac a)
    apply (simp add: obtains_step)
    apply clarify
    apply (simp add: in_possible_steps[symmetric])
    apply (simp add: drinks2_def drinks_def)
    apply clarsimp
    apply (simp add: drinks2_def[symmetric] drinks_def[symmetric])
    apply (simp add: select_def can_take apply_updates_def)
    using obtains_1_1_2 by fastforce
qed

lemma directly_subsumes: "directly_subsumes drinks2 drinks 1 1 vend_fail vend_nothing"
  apply (rule direct_subsumption[of _ _ _ _ "\<lambda>c2. c2 $ 2 = Some (Num 0)"])
   apply (simp add: obtains_1_c2)
  apply (rule subsumption)
     apply (simp add: vend_fail_def vend_nothing_def)
    apply (simp add: vend_fail_def vend_nothing_def can_take value_gt_true)
   apply (simp add: vend_fail_def vend_nothing_def)
  by (simp add: posterior_separate_def vend_fail_def vend_nothing_def)

lemma directly_subsumes_flip: "directly_subsumes drinks2 drinks 1 1 vend_nothing vend_fail"
  apply (rule direct_subsumption[of _ _ _ _ "\<lambda>c2. c2 $ 2 = Some (Num 0)"])
   apply (simp add: obtains_1_c2)
  apply (rule subsumption)
     apply (simp add: vend_fail_def vend_nothing_def)
    apply (simp add: vend_fail_def vend_nothing_def can_take value_gt_true)
   apply (simp add: vend_fail_def vend_nothing_def can_take value_gt_true)
  by (simp add: posterior_separate_def vend_fail_def vend_nothing_def)

end
