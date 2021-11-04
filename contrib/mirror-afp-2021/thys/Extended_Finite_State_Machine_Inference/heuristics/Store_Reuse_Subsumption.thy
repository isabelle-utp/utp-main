subsection\<open>Store and Reuse Subsumption\<close>
text\<open>This theory provides proofs of various properties of the \emph{store and reuse} heuristic,
including the preconditions necessary for the transitions it introduces to directly subsume their
ungeneralised counterparts.\<close>

theory Store_Reuse_Subsumption
imports Store_Reuse
begin

lemma generalisation_of_preserves:
  "is_generalisation_of t' t i r \<Longrightarrow>
    Label t = Label t' \<and>
    Arity t = Arity t' \<and>
    (Outputs t) = (Outputs t')"
  apply (simp add: is_generalisation_of_def)
  using remove_guard_add_update_preserves by auto

lemma is_generalisation_of_guard_subset:
  "is_generalisation_of t' t i r \<Longrightarrow> set (Guards t') \<subseteq> set (Guards t)"
  by (simp add: is_generalisation_of_def remove_guard_add_update_def)

lemma is_generalisation_of_medial:
  "is_generalisation_of t' t i r \<Longrightarrow>
   can_take_transition t ip rg \<longrightarrow> can_take_transition t' ip rg"
  using is_generalisation_of_guard_subset can_take_subset generalisation_of_preserves
  by (metis (no_types, lifting) can_take_def can_take_transition_def)

lemma is_generalisation_of_preserves_reg:
  "is_generalisation_of t' t i r \<Longrightarrow>
   evaluate_updates t ia c $ r = c $ r"
  by (simp add: is_generalisation_of_def r_not_updated_stays_the_same)

lemma apply_updates_foldr:
  "apply_updates u old = foldr (\<lambda>h r. r(fst h $:= aval (snd h) old)) (rev u)"
  by (simp add: apply_updates_def foldr_conv_fold)

lemma is_generalisation_of_preserves_reg_2:
  assumes gen: "is_generalisation_of t' t i r"
  and dif: "ra \<noteq> r"
shows "evaluate_updates t ia c $ ra = apply_updates (Updates t') (join_ir ia c) c $ ra"
  using assms
  apply (simp add: apply_updates_def is_generalisation_of_def remove_guard_add_update_def del: fold.simps)
  by (simp add: apply_updates_def[symmetric] apply_updates_cons)

lemma is_generalisation_of_apply_guards:
  "is_generalisation_of t' t i r \<Longrightarrow>
   apply_guards (Guards t) j \<Longrightarrow>
   apply_guards (Guards t') j"
  using is_generalisation_of_guard_subset apply_guards_subset by blast

text \<open>If we drop the guard and add an update, and the updated register is undefined in the context,
c, then the generalised transition subsumes the specific one.\<close>
lemma is_generalisation_of_subsumes_original:
  "is_generalisation_of t' t i r \<Longrightarrow>
   c $ r = None \<Longrightarrow>
   subsumes t' c t"
  apply (simp add: subsumes_def generalisation_of_preserves can_take_transition_def can_take_def posterior_separate_def)
  by (metis is_generalisation_of_apply_guards is_generalisation_of_preserves_reg is_generalisation_of_preserves_reg_2)

lemma generalise_output_posterior:
  "posterior (generalise_output t p r) i ra = posterior t i ra"
  by (simp add: can_take_def generalise_output_preserves posterior_def)

lemma generalise_output_eq: "(Outputs t) ! r = L v \<Longrightarrow>
   c $ p = Some v \<Longrightarrow>
   evaluate_outputs t i c = apply_outputs (list_update (Outputs t) r (V (R p))) (join_ir i c)"
  apply (rule nth_equalityI)
   apply (simp add: apply_outputs_preserves_length)
  subgoal for j apply (case_tac "j = r")
     apply (simp add: apply_outputs_literal apply_outputs_preserves_length apply_outputs_register)
    by (simp add: apply_outputs_preserves_length apply_outputs_unupdated)
  done

text\<open>This shows that if we can guarantee that the value of a particular register is the literal
output then the generalised output subsumes the specific output.\<close>
lemma generalise_output_subsumes_original:
  "Outputs t ! r = L v \<Longrightarrow>
   c $ p = Some v \<Longrightarrow>
   subsumes (generalise_output t p r) c t"
  by (simp add: can_take_transition_def generalise_output_def generalise_output_eq subsumes_def)

primrec stored_reused_aux_per_reg :: "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option" where
  "stored_reused_aux_per_reg t' t 0 p = (
    if is_generalised_output_of t' t 0 p then
      Some (0, p)
    else
       None
  )" |
  "stored_reused_aux_per_reg t' t (Suc r) p = (
    if is_generalised_output_of t' t (Suc r) p then
      Some (Suc r, p)
    else
      stored_reused_aux_per_reg t' t r p
  )"

primrec stored_reused_aux :: "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option" where
  "stored_reused_aux t' t r 0 = stored_reused_aux_per_reg t' t r 0" |
  "stored_reused_aux t' t r (Suc p) = (case stored_reused_aux_per_reg t' t r (Suc p) of
                                          Some x \<Rightarrow> Some x |
                                          None \<Rightarrow> stored_reused_aux t' t r p
                                        )"

definition stored_reused :: "transition \<Rightarrow> transition \<Rightarrow> (nat \<times> nat) option" where
  "stored_reused t' t = stored_reused_aux t' t (max (Transition.total_max_reg t) (Transition.total_max_reg t')) (max (length (Outputs t)) (length (Outputs t')))"

lemma stored_reused_aux_is_generalised_output_of:
"stored_reused_aux t' t mr mp = Some (p, r) \<Longrightarrow>
   is_generalised_output_of t' t p r"
proof(induct mr)
  case 0
  then show ?case
  proof(induct mp)
    case 0
    then show ?case
      apply simp
      by (metis option.distinct(1) option.inject prod.inject)
  next
    case (Suc mp)
    then show ?case
      apply (case_tac "is_generalised_output_of t' t 0 (Suc mp)")
      by auto
  qed
next
  case (Suc mr)
  then show ?case
  proof(induct mp)
    case 0
    then show ?case
      apply simp
      by (metis option.inject prod.inject)
  next
    case (Suc mp)
    then show ?case
      apply simp
      apply (case_tac "stored_reused_aux_per_reg t' t mr (Suc mp)")
       apply simp
       apply (case_tac "is_generalised_output_of t' t (Suc mr) (Suc mp)")
        apply simp
       apply simp
      apply simp
      apply (case_tac "is_generalised_output_of t' t (Suc mr) (Suc mp)")
      by auto
  qed
qed

lemma stored_reused_is_generalised_output_of:
  "stored_reused t' t = Some (p, r) \<Longrightarrow>
   is_generalised_output_of t' t p r"
  by (simp add: stored_reused_def stored_reused_aux_is_generalised_output_of)

lemma is_generalised_output_of_subsumes:
  "is_generalised_output_of t' t r p \<Longrightarrow>
   nth (Outputs t) p = L v \<Longrightarrow>
   c $ r = Some v \<Longrightarrow>
   subsumes t' c t"
  apply (simp add: subsumes_def generalise_output_preserves can_take_transition_def can_take_def posterior_separate_def)
  by (simp add: generalise_output_def generalise_output_eq is_generalised_output_of_def)

lemma lists_neq_if:
  "\<exists>i. l ! i \<noteq> l' ! i \<Longrightarrow> l \<noteq> l'"
  by auto

lemma is_generalised_output_of_does_not_subsume:
  "is_generalised_output_of t' t r p \<Longrightarrow>
   p < length (Outputs t) \<Longrightarrow>
   nth (Outputs t) p = L v \<Longrightarrow>
   c $ r \<noteq> Some v \<Longrightarrow>
   \<exists>i. can_take_transition t i c \<Longrightarrow>
   \<not>subsumes t' c t"
  apply (rule bad_outputs)
  apply clarify
  subgoal for i 
    apply (rule_tac x=i in exI)
    apply simp
    apply (rule lists_neq_if)
    apply (rule_tac x=p in exI)
    by (simp add: is_generalised_output_of_def generalise_output_def apply_outputs_nth join_ir_def)
  done

text\<open>This shows that we can use the model checker to test whether the relevant register is the
correct value for direct subsumption.\<close>
lemma generalise_output_directly_subsumes_original:
      "stored_reused t' t = Some (r, p) \<Longrightarrow>
       nth (Outputs t) p = L v \<Longrightarrow>
      (\<forall>c1 c2 t. obtains s c1 e1 0 <> t \<and> obtains s' c2 e2 0 <> t \<longrightarrow> c2 $ r = Some v) \<Longrightarrow>
       directly_subsumes e1 e2 s s' t' t"
  apply (simp add: directly_subsumes_def)
  apply standard
  by (metis is_generalised_output_of_subsumes stored_reused_aux_is_generalised_output_of stored_reused_def)

definition "generalise_output_context_check v r s1 s2 e1 e2 =
(\<forall>c1 c2 t. obtains s1 c1 (tm e1) 0 <> t \<and> obtains s2 c2 (tm e2) 0 <> t \<longrightarrow> c2 $ r = Some v)"

lemma generalise_output_context_check_directly_subsumes_original:
      "stored_reused t' t = Some (r, p) \<Longrightarrow>
       nth (Outputs t) p = L v \<Longrightarrow>
       generalise_output_context_check v r s s' e1 e2 \<Longrightarrow>
       directly_subsumes (tm e1) (tm e2) s s' t' t "
  by (simp add: generalise_output_context_check_def generalise_output_directly_subsumes_original)

definition generalise_output_direct_subsumption :: "transition \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "generalise_output_direct_subsumption t' t e e' s s' = (case stored_reused t' t of
    None \<Rightarrow> False |
    Some (r, p) \<Rightarrow>
      (case nth (Outputs t) p of
        L v \<Rightarrow> generalise_output_context_check v r s s' e e' |
        _ \<Rightarrow> False)
  )"

text\<open>This allows us to just run the two functions for quick subsumption.\<close>
lemma generalise_output_directly_subsumes_original_executable:
      "generalise_output_direct_subsumption t' t e e' s s' \<Longrightarrow>
   directly_subsumes (tm e) (tm e') s s' t' t"
  apply (simp add: generalise_output_direct_subsumption_def)
  apply (case_tac "stored_reused t' t")
   apply simp
  apply simp
  subgoal for a
    apply (case_tac a)
    apply simp
    subgoal for _ b
      apply (case_tac "Outputs t ! b")
          apply (simp add: generalise_output_context_check_directly_subsumes_original)
      by auto
    done
  done

lemma original_does_not_subsume_generalised_output:
      "stored_reused t' t = Some (p, r) \<Longrightarrow>
       r < length (Outputs t) \<Longrightarrow>
       nth (Outputs t) r = L v \<Longrightarrow>
       \<exists>a c1 tt. obtains s c1 e1 0 <> tt \<and> obtains s' a e 0 <> tt \<and> a $ p \<noteq> Some v \<and> (\<exists>i. can_take_transition t i a) \<Longrightarrow>
       \<not>directly_subsumes e1 e s s' t' t"
  apply (simp add: directly_subsumes_def)
  apply clarify
  subgoal for a c1 tt i
    apply (rule_tac x=c1 in exI)
    apply (rule_tac x=a in exI)
    using stored_reused_is_generalised_output_of[of t' t p r]
      is_generalised_output_of_does_not_subsume[of t' t p r v]
    by auto
  done

(* t' is the generalised transition *)
primrec input_i_stored_in_reg :: "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option" where
  "input_i_stored_in_reg t' t i 0 = (if is_generalisation_of t' t i 0 then Some (i, 0) else None)" |
  "input_i_stored_in_reg t' t i (Suc r) = (if is_generalisation_of t' t i (Suc r) then Some (i, (Suc r)) else input_i_stored_in_reg t' t i r)"

(* t' is the generalised transition *)
primrec input_stored_in_reg_aux :: "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option" where
  "input_stored_in_reg_aux t' t 0 r = input_i_stored_in_reg t' t 0 r" |
  "input_stored_in_reg_aux t' t (Suc i) r = (case input_i_stored_in_reg t' t (Suc i) r of
                                              None \<Rightarrow> input_i_stored_in_reg t' t i r |
                                              Some (i, r) \<Rightarrow> Some (i, r)
                                            ) "

(* t' is the generalised transition *)
definition input_stored_in_reg :: "transition \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> (nat \<times> nat) option" where
  "input_stored_in_reg t' t e = (
    case input_stored_in_reg_aux t' t (total_max_reg e) (max (Arity t) (Arity t')) of
      None \<Rightarrow> None |
      Some (i, r) \<Rightarrow>
        if length (filter (\<lambda>(r', u). r' = r) (Updates t')) = 1 then
          Some (i, r)
        else None
  )"

definition initially_undefined_context_check :: "transition_matrix \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "initially_undefined_context_check e r s = (\<forall>t a. obtains s a e 0 <> t \<longrightarrow> a $ r = None)"

lemma no_incoming_to_zero:
  "\<forall>((from, to), t)|\<in>|e. 0 < to \<Longrightarrow>
       (aaa, ba) |\<in>| possible_steps e s d l i \<Longrightarrow>
       aaa \<noteq> 0"
proof(induct e)
  case empty
  then show ?case
    by (simp add: possible_steps_def)
next
  case (insert x e)
  then show ?case
    apply (cases x)
    subgoal for a b
      apply (case_tac a)
      apply (simp add: possible_steps_def ffilter_finsert)
      subgoal for aa bb
        apply (case_tac "aa = s \<and> Label b = l \<and> length i = Arity b \<and> apply_guards (Guards b) (join_ir i d)")
         apply simp
         apply blast
        by simp
      done
    done
qed

lemma no_return_to_zero:
  "\<forall>((from, to), t)|\<in>|e. 0 < to \<Longrightarrow>
   \<forall>r n. \<not> visits 0 e (Suc n) r t"
proof(induct t)
  case Nil
  then show ?case
    by (simp add: no_further_steps)
next
  case (Cons a t)
  then show ?case
    apply clarify
    apply (rule visits.cases)
       apply simp
      apply simp
     defer
    apply simp
    apply clarify
    apply simp
    by (metis no_incoming_to_zero not0_implies_Suc)
qed

lemma no_accepting_return_to_zero:
  "\<forall>((from, to), t)|\<in>|e. to \<noteq> 0 \<Longrightarrow>
   recognises (e) (a#t) \<Longrightarrow>
   \<not>visits 0 (e) 0 <> (a#t)"
  apply clarify
  apply (rule visits.cases)
     apply simp
    apply simp
   apply clarify
  apply simp
  by (metis no_incoming_to_zero no_return_to_zero old.nat.exhaust)

lemma no_return_to_zero_must_be_empty:
  "\<forall>((from, to), t)|\<in>|e. to \<noteq> 0 \<Longrightarrow>
   obtains 0 a e s r t \<Longrightarrow>
   t = []"
proof(induct t arbitrary: s r)
case Nil
  then show ?case
    by simp
next
case (Cons a t)
  then show ?case
    apply simp
    apply (rule obtains.cases)
      apply simp
     apply simp
    by (metis (no_types, lifting) case_prodE fBexE list.inject no_further_steps no_incoming_to_zero unobtainable_if)
qed

definition "no_illegal_updates t r = (\<forall>u \<in> set (Updates t). fst u \<noteq> r)"

lemma input_stored_in_reg_aux_is_generalisation_aux:
  "input_stored_in_reg_aux t' t mr mi = Some (i, r) \<Longrightarrow>
   is_generalisation_of t' t i r"
proof(induct mi)
  case 0
  then show ?case
  proof(induct mr)
    case 0
    then show ?case
      apply (case_tac "is_generalisation_of t' t 0 0")
      by auto
  next
    case (Suc mr)
    then show ?case
      apply simp
      apply (case_tac "is_generalisation_of t' t (Suc mr) 0")
       apply simp
      apply simp
      apply (case_tac "is_generalisation_of t' t mr 0")
      by auto
  qed
next
  case (Suc mi)
  then show ?case
  proof(induct mr)
    case 0
    then show ?case
      apply (case_tac "is_generalisation_of t' t 0 (Suc mi)")
      by auto
  next
    case (Suc mr)
    then show ?case
      apply simp
      apply (case_tac "is_generalisation_of t' t (Suc mr) (Suc mi)")
       apply simp
      apply simp
      apply (case_tac "input_i_stored_in_reg t' t (Suc mr) mi")
       apply simp
       apply (case_tac "is_generalisation_of t' t mr (Suc mi)")
      by auto
  qed
qed

lemma input_stored_in_reg_is_generalisation:
  "input_stored_in_reg t' t e = Some (i, r) \<Longrightarrow> is_generalisation_of t' t i r"
  apply (simp add: input_stored_in_reg_def)
  apply (cases "input_stored_in_reg_aux t' t (total_max_reg e) (max (Arity t) (Arity t'))")
   apply simp
  subgoal for a 
    apply (case_tac a)
    apply simp
    subgoal for _ b
      apply (case_tac "length (filter (\<lambda>(r', u). r' = b) (Updates t')) = 1")
       apply (simp add: input_stored_in_reg_aux_is_generalisation_aux)
      by simp
    done
  done

(*
  This allows us to call these three functions for direct subsumption of generalised
*)
lemma generalised_directly_subsumes_original:
  "input_stored_in_reg t' t e = Some (i, r) \<Longrightarrow>
   initially_undefined_context_check (tm e) r s' \<Longrightarrow>
   no_illegal_updates t r \<Longrightarrow>
   directly_subsumes (tm e1) (tm e) s s' t' t"
  apply (simp add: directly_subsumes_def)
  apply standard
  apply (meson finfun_const.rep_eq input_stored_in_reg_is_generalisation is_generalisation_of_subsumes_original)
  apply (rule is_generalisation_of_subsumes_original)
  using input_stored_in_reg_is_generalisation apply blast
  by (simp add: initially_undefined_context_check_def)

definition drop_guard_add_update_direct_subsumption :: "transition \<Rightarrow> transition \<Rightarrow> iEFSM \<Rightarrow> nat \<Rightarrow> bool" where
  "drop_guard_add_update_direct_subsumption t' t e s' = (
    case input_stored_in_reg t' t e of
      None \<Rightarrow> False |
      Some (i, r) \<Rightarrow>
        if no_illegal_updates t r then
          initially_undefined_context_check (tm e) r s'
        else False
    )"

lemma drop_guard_add_update_direct_subsumption_implies_direct_subsumption:
  "drop_guard_add_update_direct_subsumption t' t e s' \<Longrightarrow>
   directly_subsumes (tm e1) (tm e) s s' t' t"
  apply (simp add: drop_guard_add_update_direct_subsumption_def)
  apply (case_tac "input_stored_in_reg t' t e")
   apply simp+
  subgoal for a
    apply (case_tac a)
    apply simp
    subgoal for _ b
      apply (case_tac "no_illegal_updates t b")
       apply (simp add: generalised_directly_subsumes_original)
      by simp
    done
  done

lemma is_generalisation_of_constrains_input:
  "is_generalisation_of t' t i r \<Longrightarrow>
   \<exists>v. gexp.Eq (V (vname.I i)) (L v) \<in> set (Guards t)"
  by (simp add: is_generalisation_of_def)

lemma is_generalisation_of_derestricts_input:
  "is_generalisation_of t' t i r \<Longrightarrow>
   \<forall>g \<in> set (Guards t'). \<not> gexp_constrains g (V (vname.I i))"
  by (simp add: is_generalisation_of_def remove_guard_add_update_def)

lemma is_generalisation_of_same_arity:
  "is_generalisation_of t' t i r \<Longrightarrow> Arity t = Arity t'"
  by (simp add: is_generalisation_of_def remove_guard_add_update_def)

lemma is_generalisation_of_i_lt_arity:
  "is_generalisation_of t' t i r \<Longrightarrow> i < Arity t"
  by (simp add: is_generalisation_of_def)

lemma "\<forall>i. \<not> can_take_transition t i r \<and> \<not> can_take_transition t' i r \<Longrightarrow>
       Label t = Label t' \<Longrightarrow>
       Arity t = Arity t' \<Longrightarrow>
       subsumes t' r t"
  by (simp add: subsumes_def posterior_separate_def can_take_transition_def)

lemma input_not_constrained_aval_swap_inputs:
  "\<not> aexp_constrains a (V (I v)) \<Longrightarrow> aval a (join_ir i c) = aval a (join_ir (list_update i v x) c)"
  apply(induct a rule: aexp_induct_separate_V_cases)
       apply simp
      apply (metis aexp_constrains.simps(2) aval.simps(2) input2state_nth input2state_out_of_bounds join_ir_def length_list_update not_le nth_list_update_neq vname.simps(5))
  using join_ir_def by auto

lemma aval_unconstrained:
  " \<not> aexp_constrains a (V (vname.I i)) \<Longrightarrow>
  i < length ia \<Longrightarrow>
  v = ia ! i \<Longrightarrow>
  v' \<noteq> v \<Longrightarrow>
  aval a (join_ir ia c) = aval a (join_ir (list_update ia i v') c)"
  apply(induct a rule: aexp_induct_separate_V_cases)
  using input_not_constrained_aval_swap_inputs by blast+

lemma input_not_constrained_gval_swap_inputs:
  "\<not> gexp_constrains a (V (I v)) \<Longrightarrow>
   gval a (join_ir i c) = gval a (join_ir (i[v := x]) c)"
proof(induct a)
  case (Bc x)
  then show ?case
    by (metis (full_types) gval.simps(1) gval.simps(2))
next
  case (Eq x1a x2)
  then show ?case
    using input_not_constrained_aval_swap_inputs by auto
next
  case (Gt x1a x2)
  then show ?case
    using input_not_constrained_aval_swap_inputs by auto
next
  case (In x1a x2)
  then show ?case
    apply simp
    apply (case_tac "join_ir i c x1a")
     apply simp
     apply (case_tac "join_ir (i[v := x]) c x1a")
      apply simp
     apply simp
     apply (metis aexp.inject(2) aexp_constrains.simps(2) aval.simps(2) input_not_constrained_aval_swap_inputs option.discI)
    apply (case_tac "join_ir i c x1a")
     apply simp
     apply (case_tac "join_ir (i[v := x]) c x1a")
     apply simp
     apply (metis aexp.inject(2) aexp_constrains.simps(2) aval.simps(2) input_not_constrained_aval_swap_inputs option.discI)
    apply simp
    by (metis (no_types, lifting) datastate(1) input2state_within_bounds join_ir_R join_ir_nth le_less_linear list_update_beyond nth_list_update option.inject vname.case(1) vname.exhaust)
qed auto

text\<open>If input $i$ is stored in register $r$ by transition $t$ then if we can take transition,
$t^\prime$ then for some input $ia$ then transition $t$ does not subsume $t^\prime$.\<close>
lemma input_stored_in_reg_not_subsumed:
  "input_stored_in_reg t' t e = Some (i, r) \<Longrightarrow>
   \<exists>ia. can_take_transition t' ia c \<Longrightarrow>
   \<not> subsumes t c t'"
  using input_stored_in_reg_is_generalisation[of t' t e i r]
  using is_generalisation_of_constrains_input[of t' t i r]
  using is_generalisation_of_derestricts_input[of t' t i r]
  apply simp
  apply (rule bad_guards)
  apply clarify
  subgoal for ia v
    apply (simp add: can_take_transition_def can_take_def)
    apply clarify
    apply (case_tac "v")
    subgoal for x1
      apply (rule_tac x="list_update ia i (Str _)" in exI)
      apply simp
      apply standard
       apply (simp add: apply_guards_def)
       apply (metis input_not_constrained_gval_swap_inputs)
      apply (simp add: apply_guards_def Bex_def)
      apply standard
      apply (rule_tac x="Eq (V (vname.I i)) (L (Num x1))" in exI)
      apply (simp add: join_ir_def input2state_nth is_generalisation_of_i_lt_arity str_not_num)
      done
    subgoal for x2
      apply (rule_tac x="list_update ia i (Num _)" in exI)
      apply simp
      apply standard
       apply (simp add: apply_guards_def)
       apply (metis input_not_constrained_gval_swap_inputs)
      apply (simp add: apply_guards_def Bex_def)
      apply standard
      apply (rule_tac x="Eq (V (vname.I i)) (L (value.Str x2))" in exI)
      by (simp add: join_ir_def input2state_nth is_generalisation_of_i_lt_arity str_not_num)
    done
  done

lemma aval_updated:
  "(r, u) \<in> set U \<Longrightarrow>
   r \<notin> set (map fst (removeAll (r, u) U)) \<Longrightarrow>
   apply_updates U s c $ r = aval u s"
proof(induct U rule: rev_induct)
  case (snoc a U)
  then show ?case
    apply (case_tac "(r, u) = a")
    using apply_updates_foldr by auto
qed auto

lemma can_take_append_subset:
  "set (Guards t') \<subset> set (Guards t) \<Longrightarrow>
can_take a (Guards t @ Guards t') ia c = can_take a (Guards t) ia c"
  by (metis apply_guards_append apply_guards_subset_append can_take_def dual_order.strict_implies_order)

text\<open>Transitions of the form $t = \textit{select}:1[i_0=x]$ do not subsume transitions
of the form $t^\prime = select:1/r_1:=i_1$.\<close>
lemma general_not_subsume_orig: "Arity t' = Arity t \<Longrightarrow>
   set (Guards t') \<subset> set (Guards t) \<Longrightarrow>
   (r, (V (I i))) \<in> set (Updates t') \<Longrightarrow>
   r \<notin> set (map fst (removeAll (r, V (I i)) (Updates t'))) \<Longrightarrow>
   r \<notin> set (map fst (Updates t)) \<Longrightarrow>
   \<exists>i. can_take_transition t i c \<Longrightarrow>
   c $ r = None \<Longrightarrow>
   i < Arity t \<Longrightarrow>
   \<not> subsumes t c t'"
  apply (rule inconsistent_updates)
  apply (erule_tac exE)
  subgoal for ia
    apply (rule_tac x="evaluate_updates t ia c" in exI)
    apply (rule_tac x="apply_updates (Updates t') (join_ir ia c) c" in exI)
    apply standard
     apply (rule_tac x=ia in exI)
     apply (metis can_take_def can_take_transition_def can_take_subset posterior_separate_def psubsetE)
    apply (rule_tac x=r in exI)
    apply (simp add: r_not_updated_stays_the_same)
    apply (rule_tac x="\<lambda>x. x = None" in exI)
    by (simp add: aval_updated can_take_transition_def can_take_def)
  done

lemma input_stored_in_reg_updates_reg:
  "input_stored_in_reg t2 t1 a = Some (i, r) \<Longrightarrow>
   (r, V (I i)) \<in> set (Updates t2)"
  using input_stored_in_reg_is_generalisation[of t2 t1 a i r]
  apply simp
  by (simp add: is_generalisation_of_def remove_guard_add_update_def)

definition "diff_outputs_ctx e1 e2 s1 s2 t1 t2 =
  (if Outputs t1 = Outputs t2 then False else
  (\<exists>p c1 r. obtains s1 c1 e1 0 <> p \<and>
       obtains s2 r e2 0 <> p \<and>
       (\<exists>i. can_take_transition t1 i r \<and> can_take_transition t2 i r \<and>
       evaluate_outputs t1 i r \<noteq> evaluate_outputs t2 i r)
  ))"

lemma diff_outputs_direct_subsumption:
  "diff_outputs_ctx e1 e2 s1 s2 t1 t2 \<Longrightarrow>
   \<not> directly_subsumes e1 e2 s1 s2 t1 t2"
  apply (simp add: directly_subsumes_def diff_outputs_ctx_def)
  apply (case_tac "Outputs t1 = Outputs t2")
   apply simp
  apply clarsimp
  subgoal for _ c1 r
    apply (rule_tac x=c1 in exI)
    apply (rule_tac x=r in exI)
    using bad_outputs by force
  done

definition not_updated :: "nat \<Rightarrow> transition \<Rightarrow> bool" where
  "not_updated r t = (filter (\<lambda>(r', _). r' = r) (Updates t) = [])"

lemma not_updated: assumes "not_updated r t2"
  shows "apply_updates (Updates t2) s s' $ r = s' $ r"
proof-
  have not_updated_aux: "\<And>t2. filter (\<lambda>(r', _). r' = r) t2 = [] \<Longrightarrow>
   apply_updates t2 s s' $ r = s' $ r"
    apply (rule r_not_updated_stays_the_same)
    by (metis (mono_tags, lifting) filter_empty_conv imageE prod.case_eq_if)
  show ?thesis
    using assms
    by (simp add: not_updated_def not_updated_aux)
qed

lemma one_extra_update_subsumes: "Label t1 = Label t2 \<Longrightarrow>
   Arity t1 = Arity t2 \<Longrightarrow>
   set (Guards t1) \<subseteq> set (Guards t2) \<Longrightarrow>
   Outputs t1 = Outputs t2 \<Longrightarrow>
   Updates t1 = (r, u) # Updates t2 \<Longrightarrow>
   not_updated r t2 \<Longrightarrow>
   c $ r = None \<Longrightarrow>
   subsumes t1 c t2"
  apply (simp add: subsumes_def posterior_separate_def can_take_transition_def can_take_def)
  by (metis apply_guards_subset apply_updates_cons not_updated)

lemma one_extra_update_directly_subsumes:
  "Label t1 = Label t2 \<Longrightarrow>
   Arity t1 = Arity t2 \<Longrightarrow>
   set (Guards t1) \<subseteq> set (Guards t2) \<Longrightarrow>
   Outputs t1 = Outputs t2 \<Longrightarrow>
   Updates t1 = (r, u)#(Updates t2) \<Longrightarrow>
   not_updated r t2 \<Longrightarrow>
   initially_undefined_context_check e2 r s2 \<Longrightarrow>
   directly_subsumes e1 e2 s1 s2 t1 t2"
  apply (simp add: directly_subsumes_def)
  apply standard
   apply (meson one_extra_update_subsumes finfun_const_apply)
  apply (simp add: initially_undefined_context_check_def)
  using obtainable_def one_extra_update_subsumes by auto

definition "one_extra_update t1 t2 s2 e2 = (
  Label t1 = Label t2 \<and>
  Arity t1 = Arity t2 \<and>
  set (Guards t1) \<subseteq> set (Guards t2) \<and>
  Outputs t1 = Outputs t2 \<and>
  Updates t1 \<noteq> [] \<and>
  tl (Updates t1) = (Updates t2) \<and>
  (\<exists>r \<in> set (map fst (Updates t1)). fst (hd (Updates t1)) = r \<and>
  not_updated r t2 \<and>
  initially_undefined_context_check e2 r s2)
)"

lemma must_be_an_update:
  "U1 \<noteq> [] \<Longrightarrow>
   fst (hd U1) = r \<and> tl U1 = U2 \<Longrightarrow>
   \<exists>u. U1 = (r, u)#(U2)"
  by (metis eq_fst_iff hd_Cons_tl)

lemma one_extra_update_direct_subsumption:
  "one_extra_update t1 t2 s2 e2 \<Longrightarrow> directly_subsumes e1 e2 s1 s2 t1 t2"
  apply (insert must_be_an_update[of "Updates t1" r "Updates t2"])
  apply (simp add: one_extra_update_def)
  by (metis eq_fst_iff hd_Cons_tl one_extra_update_directly_subsumes)

end
