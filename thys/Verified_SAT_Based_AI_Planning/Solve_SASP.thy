(*
  Author: Mohammad Abdulaziz
*)

theory Solve_SASP
  imports AST_SAS_Plus_Equivalence "SAT_Solve_SAS_Plus" 
          "HOL-Data_Structures.RBT_Map" "HOL-Library.Code_Target_Nat" HOL.String
          AI_Planning_Languages_Semantics.SASP_Checker Set2_Join_RBT
begin

subsection \<open>SAT encoding works for Fast-Downward's representation\<close>

context abs_ast_prob
begin

theorem is_serial_sol_then_valid_plan_encoded:
  "\<A> \<Turnstile> \<Phi>\<^sub>\<forall> (\<phi> (prob_with_noop abs_prob)) t \<Longrightarrow>
   valid_plan 
        (decode_abs_plan
           (rem_noops
                   (map (\<lambda>op. \<phi>\<^sub>O\<inverse> (prob_with_noop abs_prob) op)
                        (concat (\<Phi>\<inverse> (\<phi> (prob_with_noop abs_prob)) \<A> t)))))"
  by (fastforce intro!: is_serial_sol_then_valid_plan abs_prob_valid
                        sas_plus_problem_has_serial_solution_iff_i')
  
lemma length_abs_ast_plan: "length \<pi>s = length (abs_ast_plan \<pi>s)"
  by (auto simp: abs_ast_plan_def)

theorem valid_plan_then_is_serial_sol_encoded:
  "valid_plan \<pi>s \<Longrightarrow> length \<pi>s \<le>  h \<Longrightarrow> \<exists>\<A>. \<A> \<Turnstile> \<Phi>\<^sub>\<forall> (\<phi> (prob_with_noop abs_prob)) h"
  apply(subst (asm) length_abs_ast_plan)
  by (fastforce intro!: sas_plus_problem_has_serial_solution_iff_ii' abs_prob_valid
                        valid_plan_then_is_serial_sol)
end

section \<open>DIMACS-like semantics for CNF formulae\<close>

text \<open>We now push the SAT encoding towards a lower-level representation by replacing the atoms which
      have variable IDs and time steps into natural numbers.\<close>

lemma gtD: "((l::nat) < n) \<Longrightarrow> (\<exists>m. n = Suc m \<and> l \<le> m)"
  by (induction n) auto

locale cnf_to_dimacs =
  fixes h :: nat and n_ops :: nat
begin

fun var_to_dimacs where
  "var_to_dimacs (Operator t k) = 1 + t + k * h"
| "var_to_dimacs (State t k) = 1 + n_ops * h + t + k * (h)"

definition dimacs_to_var where
  "dimacs_to_var v \<equiv>
     if v < 1 + n_ops * h then
       Operator ((v - 1) mod (h)) ((v - 1) div (h))
     else
       (let k = ((v - 1) - n_ops * h) in 
          State (k mod (h)) (k div (h)))"

fun valid_state_var where
  "valid_state_var (Operator t k) \<longleftrightarrow> t < h \<and> k < n_ops"
| "valid_state_var (State t k) \<longleftrightarrow> t < h"

lemma State_works:
"valid_state_var (State t k) \<Longrightarrow>
      dimacs_to_var (var_to_dimacs (State t k)) = 
         (State t k)"
  by (induction k) (auto simp add: dimacs_to_var_def add.left_commute Let_def)

lemma Operator_works:
   "valid_state_var (Operator t k) \<Longrightarrow>
      dimacs_to_var (var_to_dimacs (Operator t k)) = 
         (Operator t k)"
  by (induction k) (auto simp add: algebra_simps dimacs_to_var_def gr0_conv_Suc nat_le_iff_add dest!: gtD)

lemma sat_plan_to_dimacs_works:
  "valid_state_var sv \<Longrightarrow>
     dimacs_to_var (var_to_dimacs sv) = sv"
  apply(cases sv)
  using State_works Operator_works
  by auto

end

lemma changing_atoms_works:
  "(\<And>x. P x \<Longrightarrow> (f o g) x = x) \<Longrightarrow> (\<forall>x\<in>atoms phi. P x) \<Longrightarrow> M \<Turnstile> phi \<longleftrightarrow> M o f \<Turnstile> map_formula g phi"  
  by (induction phi) auto  

lemma changing_atoms_works':
  "M o g \<Turnstile> phi \<longleftrightarrow> M  \<Turnstile> map_formula g phi"  
  by (induction phi) auto  

context cnf_to_dimacs
begin

lemma sat_plan_to_dimacs:
  "(\<And>sv. sv\<in>atoms sat_plan_formula \<Longrightarrow> valid_state_var sv) \<Longrightarrow>
       M \<Turnstile> sat_plan_formula
         \<longleftrightarrow> M o dimacs_to_var \<Turnstile> map_formula var_to_dimacs sat_plan_formula"
  by(auto intro!: changing_atoms_works[where P = valid_state_var] simp: sat_plan_to_dimacs_works)

lemma dimacs_to_sat_plan:
  "M o var_to_dimacs \<Turnstile> sat_plan_formula
     \<longleftrightarrow> M \<Turnstile> map_formula var_to_dimacs sat_plan_formula"
  using changing_atoms_works' .

end

locale sat_solve_sasp = abs_ast_prob "\<Pi>" + cnf_to_dimacs "Suc h" "Suc (length ast\<delta>)"
  for \<Pi> h
begin

lemma encode_initial_state_valid: 
  "sv \<in> atoms (encode_initial_state Prob) \<Longrightarrow> valid_state_var sv"
  by (auto simp add: encode_state_variable_def Let_def encode_initial_state_def split: sat_plan_variable.splits bool.splits)

lemma length_operators: "length (operators_of (\<phi> (prob_with_noop abs_prob))) = Suc (length ast\<delta>)"
  by(simp add: abs_prob_def abs_ast_operator_section_def sas_plus_problem_to_strips_problem_def prob_with_noop_def)

lemma encode_operator_effect_valid_1: "t < h \<Longrightarrow> op \<in> set (operators_of (\<phi> (prob_with_noop abs_prob))) \<Longrightarrow> 
       sv \<in> atoms 
        (\<^bold>\<And>(map (\<lambda>v. 
              \<^bold>\<not>(Atom (Operator t (index (operators_of (\<phi> (prob_with_noop abs_prob))) op)))
              \<^bold>\<or> Atom (State (Suc t) (index vs v))) 
            asses)) \<Longrightarrow>
       valid_state_var sv"
  using length_operators
  by (induction asses) (auto simp: simp add: cnf_to_dimacs.valid_state_var.simps)
  
  
lemma encode_operator_effect_valid_2: "t < h \<Longrightarrow> op \<in> set (operators_of (\<phi> (prob_with_noop abs_prob))) \<Longrightarrow>
       sv \<in> atoms 
        (\<^bold>\<And>(map (\<lambda>v.
              \<^bold>\<not>(Atom (Operator t (index (operators_of (\<phi> (prob_with_noop abs_prob))) op)))
               \<^bold>\<or> \<^bold>\<not> (Atom (State (Suc t) (index vs v))))
            asses)) \<Longrightarrow>
       valid_state_var sv"
  using length_operators
  by (induction asses) (auto simp: simp add: cnf_to_dimacs.valid_state_var.simps)

end

lemma atoms_And_append: "atoms (\<^bold>\<And> (as1 @ as2)) = atoms (\<^bold>\<And> as1) \<union>  atoms (\<^bold>\<And> as2)"
  by (induction as1) auto

context sat_solve_sasp
begin

lemma encode_operator_effect_valid: 
  "sv \<in> atoms (encode_operator_effect (\<phi> (prob_with_noop abs_prob)) t op) \<Longrightarrow> 
    t < h \<Longrightarrow> op \<in> set (operators_of (\<phi> (prob_with_noop abs_prob))) \<Longrightarrow>
    valid_state_var sv"
  by (force simp: encode_operator_effect_def Let_def atoms_And_append 
            intro!: encode_operator_effect_valid_1 encode_operator_effect_valid_2)

end

lemma foldr_And: "foldr (\<^bold>\<and>) as (\<^bold>\<not> \<bottom>) = (\<^bold>\<And> as)"
  by (induction as) auto

context sat_solve_sasp
begin

lemma encode_all_operator_effects_valid:
   "t < Suc h \<Longrightarrow>
    sv \<in> atoms (encode_all_operator_effects (\<phi> (prob_with_noop abs_prob)) (operators_of (\<phi> (prob_with_noop abs_prob))) t) \<Longrightarrow> 
    valid_state_var sv"
  unfolding encode_all_operator_effects_def foldr_And 
  by (force simp add: encode_operator_effect_valid)

lemma encode_operator_precondition_valid_1: 
  "t < h \<Longrightarrow> op \<in> set (operators_of (\<phi> (prob_with_noop abs_prob))) \<Longrightarrow> 
       sv \<in> atoms 
        (\<^bold>\<And>(map (\<lambda>v. 
        \<^bold>\<not> (Atom (Operator t (index (operators_of (\<phi> (prob_with_noop abs_prob))) op))) \<^bold>\<or> Atom (State t (f v))) 
      asses)) \<Longrightarrow>
       valid_state_var sv"
  using length_operators
  by (induction asses) (auto simp: simp add: cnf_to_dimacs.valid_state_var.simps)
  
lemma encode_operator_precondition_valid: 
  "sv \<in> atoms (encode_operator_precondition (\<phi> (prob_with_noop abs_prob)) t op) \<Longrightarrow> 
    t < h \<Longrightarrow> op \<in> set (operators_of (\<phi> (prob_with_noop abs_prob))) \<Longrightarrow>
    valid_state_var sv"
  by (force simp: encode_operator_precondition_def Let_def 
            intro!: encode_operator_precondition_valid_1)

lemma encode_all_operator_preconditions_valid:
   "t < Suc h \<Longrightarrow>
    sv \<in> atoms (encode_all_operator_preconditions (\<phi> (prob_with_noop abs_prob)) (operators_of (\<phi> (prob_with_noop abs_prob))) t) \<Longrightarrow> 
    valid_state_var sv"
  unfolding encode_all_operator_preconditions_def foldr_And 
  by (force simp add: encode_operator_precondition_valid)

lemma encode_operators_valid:
   "sv \<in> atoms (encode_operators (\<phi> (prob_with_noop abs_prob)) t) \<Longrightarrow> t < Suc h \<Longrightarrow>
    valid_state_var sv" 
  unfolding encode_operators_def Let_def 
  by (force simp add: encode_all_operator_preconditions_valid encode_all_operator_effects_valid)

lemma encode_negative_transition_frame_axiom':
  "t < h \<Longrightarrow>
   set deleting_operators \<subseteq> set (operators_of (\<phi> (prob_with_noop abs_prob))) \<Longrightarrow>
    sv \<in> atoms 
       (\<^bold>\<not>(Atom (State t v_idx)) 
          \<^bold>\<or> (Atom (State (Suc t) v_idx)
          \<^bold>\<or> \<^bold>\<Or> (map (\<lambda>op. Atom (Operator t (index (operators_of (\<phi> (prob_with_noop abs_prob))) op)))
          deleting_operators))) \<Longrightarrow> 
    valid_state_var sv"
  by (induction deleting_operators) (auto simp: length_operators[symmetric] cnf_to_dimacs.valid_state_var.simps)

lemma encode_negative_transition_frame_axiom_valid:
  "sv \<in> atoms (encode_negative_transition_frame_axiom (\<phi> (prob_with_noop abs_prob)) t v) \<Longrightarrow>  t < h \<Longrightarrow> 
    valid_state_var sv"
  unfolding encode_negative_transition_frame_axiom_def Let_def
  apply(intro encode_negative_transition_frame_axiom'[of t])
  by auto

lemma encode_positive_transition_frame_axiom_valid:
  "sv \<in> atoms (encode_positive_transition_frame_axiom (\<phi> (prob_with_noop abs_prob)) t v) \<Longrightarrow> t < h \<Longrightarrow> 
    valid_state_var sv"
  unfolding encode_positive_transition_frame_axiom_def Let_def
  apply(intro encode_negative_transition_frame_axiom'[of t])
  by auto

lemma encode_all_frame_axioms_valid:
  "sv \<in> atoms (encode_all_frame_axioms (\<phi> (prob_with_noop abs_prob)) t) \<Longrightarrow> t < Suc h \<Longrightarrow>
    valid_state_var sv"
  unfolding encode_all_frame_axioms_def Let_def atoms_And_append
  by (force simp add: encode_negative_transition_frame_axiom_valid encode_positive_transition_frame_axiom_valid)

lemma encode_goal_state_valid: 
  "sv \<in> atoms (encode_goal_state Prob t) \<Longrightarrow> t < Suc h \<Longrightarrow> valid_state_var sv"
  by (auto simp add: encode_state_variable_def Let_def encode_goal_state_def split: sat_plan_variable.splits bool.splits)

lemma encode_problem_valid:
  "sv \<in> atoms (encode_problem (\<phi> (prob_with_noop abs_prob)) h) \<Longrightarrow> valid_state_var sv"
  unfolding encode_problem_def
  using encode_initial_state_valid encode_operators_valid encode_all_frame_axioms_valid encode_goal_state_valid
  by fastforce

lemma encode_interfering_operator_pair_exclusion_valid:
  "sv \<in> atoms (encode_interfering_operator_pair_exclusion (\<phi> (prob_with_noop abs_prob)) t op\<^sub>1 op\<^sub>2) \<Longrightarrow> t < Suc h \<Longrightarrow> 
       op\<^sub>1 \<in> set (operators_of (\<phi> (prob_with_noop abs_prob))) \<Longrightarrow> op\<^sub>2 \<in> set (operators_of (\<phi> (prob_with_noop abs_prob))) \<Longrightarrow>       
       valid_state_var sv"
  by (auto simp: encode_interfering_operator_pair_exclusion_def Let_def length_operators[symmetric] cnf_to_dimacs.valid_state_var.simps)

lemma encode_interfering_operator_exclusion_valid: 
  "sv \<in> atoms (encode_interfering_operator_exclusion (\<phi> (prob_with_noop abs_prob)) t) \<Longrightarrow> t < Suc h \<Longrightarrow> 
      valid_state_var sv"
  unfolding encode_interfering_operator_exclusion_def Let_def foldr_And
  by (force simp add: encode_interfering_operator_pair_exclusion_valid)

lemma encode_problem_with_operator_interference_exclusion_valid:
  "sv \<in> atoms (encode_problem_with_operator_interference_exclusion (\<phi> (prob_with_noop abs_prob)) h) \<Longrightarrow> valid_state_var sv"
  unfolding encode_problem_with_operator_interference_exclusion_def
  using encode_initial_state_valid encode_operators_valid encode_all_frame_axioms_valid encode_goal_state_valid
        encode_interfering_operator_exclusion_valid
  by fastforce

lemma planning_by_cnf_dimacs_complete:
  "valid_plan \<pi>s \<Longrightarrow> length \<pi>s \<le> h \<Longrightarrow>
     \<exists>M. M \<Turnstile> map_formula var_to_dimacs (\<Phi>\<^sub>\<forall> (\<phi> (prob_with_noop  abs_prob)) h)"
  using valid_plan_then_is_serial_sol_encoded
        sat_plan_to_dimacs[OF encode_problem_with_operator_interference_exclusion_valid]
  by meson

lemma planning_by_cnf_dimacs_sound:
  "\<A> \<Turnstile> map_formula var_to_dimacs (\<Phi>\<^sub>\<forall> (\<phi> (prob_with_noop abs_prob)) t) \<Longrightarrow>
   valid_plan 
        (decode_abs_plan
           (rem_noops
             (map (\<lambda>op. \<phi>\<^sub>O\<inverse> (prob_with_noop abs_prob) op) 
                (concat (\<Phi>\<inverse> (\<phi> (prob_with_noop abs_prob)) (\<A> o var_to_dimacs) t)))))"
  using changing_atoms_works'
  by (fastforce intro!: is_serial_sol_then_valid_plan_encoded)

end

subsection \<open>Going from Formualae to DIMACS-like CNF\<close>

text \<open>We now represent the CNF formulae into a very low-level representation that is reminiscent to
      the DIMACS representation, where a CNF formula is a list of list of integers.\<close>

fun disj_to_dimacs::"nat formula \<Rightarrow> int list" where
  "disj_to_dimacs (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) = disj_to_dimacs \<phi>\<^sub>1 @ disj_to_dimacs \<phi>\<^sub>2"
| "disj_to_dimacs \<bottom> = []"
| "disj_to_dimacs (Not \<bottom>) = [-1::int,1::int]"
| "disj_to_dimacs (Atom v) = [int v]"
| "disj_to_dimacs (Not (Atom v)) = [-(int v)]"

fun cnf_to_dimacs::"nat formula \<Rightarrow> int list list" where
  "cnf_to_dimacs (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) = cnf_to_dimacs \<phi>\<^sub>1 @ cnf_to_dimacs \<phi>\<^sub>2"
| "cnf_to_dimacs d = [disj_to_dimacs d]"

definition "dimacs_lit_to_var l \<equiv> nat (abs l)"

definition "find_max (xs::nat list)\<equiv> (fold max xs 1)"

lemma find_max_works:
"x \<in> set xs \<Longrightarrow> x \<le> find_max xs" (is "?P \<Longrightarrow> ?Q")
proof-
  have "x \<in> set xs \<Longrightarrow> (x::nat) \<le> (fold max xs m)" for m
    unfolding max_def
    apply (induction xs arbitrary: m rule: rev_induct)
    using nat_le_linear
    by (auto dest:  le_trans simp add:)
  thus "?P \<Longrightarrow> ?Q"
    by(auto simp add: find_max_def max_def)
qed

fun formula_vars where
"formula_vars (\<bottom>) = []" |
"formula_vars (Atom k) = [k]" |
"formula_vars (Not F) = formula_vars F" |
"formula_vars (And F G) = formula_vars F @ formula_vars G" |
"formula_vars (Imp F G) = formula_vars F @ formula_vars G" |
"formula_vars (Or F G) = formula_vars F @ formula_vars G"

lemma atoms_formula_vars: "atoms f = set (formula_vars f)"
  by (induction f) auto

lemma max_var: "v \<in> atoms (f::nat formula) \<Longrightarrow> v \<le> find_max (formula_vars f)"
  using find_max_works
  by(simp add: atoms_formula_vars)

definition "dimacs_max_var cs \<equiv> find_max (map (find_max o (map (nat o abs))) cs)"

lemma fold_max_ge: "b \<le> a \<Longrightarrow> (b::nat) \<le> fold (\<lambda>x m. if m \<le> x then x else m) ys a"
  by (induction ys arbitrary: a b) auto

lemma find_max_append:  "find_max (xs @ ys) = max (find_max xs) (find_max ys) "
  apply(simp only: Max.set_eq_fold[symmetric] append_Cons[symmetric] set_append find_max_def)
  by (metis List.finite_set Max.union Un_absorb Un_insert_left Un_insert_right list.distinct(1) list.simps(15) set_empty)

definition dimacs_model::"int list \<Rightarrow> int list list \<Rightarrow> bool" where
  "dimacs_model ls cs \<equiv> (\<forall>c\<in>set cs. (\<exists>l\<in>set ls. l \<in> set c)) \<and>
                              distinct (map dimacs_lit_to_var ls)"

fun model_to_dimacs_model where
  "model_to_dimacs_model M (v#vs) = (if M v then int v else - (int v)) # (model_to_dimacs_model M vs)"
| "model_to_dimacs_model _ [] = []"

lemma model_to_dimacs_model_append:
 "set (model_to_dimacs_model M (vs @ vs')) = set (model_to_dimacs_model M vs) \<union> set (model_to_dimacs_model M vs')"
  by (induction vs) auto

lemma upt_append_sing: "xs @ [x] = [a..<n_vars] \<Longrightarrow> a < n_vars \<Longrightarrow> (xs = [a..<n_vars - 1] \<and> x = n_vars-1 \<and> n_vars > 0)"
  by (induction "n_vars") auto

lemma upt_eqD: "upt a b = upt a b' \<Longrightarrow> (b = b' \<or> b' \<le> a \<or> b \<le> a)"
  by (induction b) (auto dest!: upt_append_sing split: if_splits)

lemma pos_in_model: "M n \<Longrightarrow> 0 < n \<Longrightarrow> n < n_vars \<Longrightarrow> int n \<in> set (model_to_dimacs_model M [1..<n_vars])"
  by (induction n_vars) (auto simp add: less_Suc_eq model_to_dimacs_model_append )

lemma neg_in_model: "\<not> M n \<Longrightarrow> 0 < n \<Longrightarrow> n < n_vars \<Longrightarrow> - (int n) \<in> set (model_to_dimacs_model M [1..<n_vars])"
  by (induction n_vars) (auto simp add: less_Suc_eq model_to_dimacs_model_append)

lemma in_model: "0 < n \<Longrightarrow> n < n_vars \<Longrightarrow> int n \<in> set (model_to_dimacs_model M [1..<n_vars]) \<or> - (int n) \<in> set (model_to_dimacs_model M [1..<n_vars])"
  using pos_in_model neg_in_model
  by metis

lemma model_to_dimacs_model_all_vars:
  "(\<forall>v\<in>atoms f. 0 < v \<and> v < n_vars) \<Longrightarrow> is_cnf f \<Longrightarrow> M \<Turnstile> f \<Longrightarrow>
        (\<forall>n<n_vars. 0 < n \<longrightarrow> (int n \<in> set (model_to_dimacs_model M [(1::nat)..<n_vars]) \<or>
                              -(int n) \<in> set (model_to_dimacs_model M [(1::nat)..<n_vars])))"
  using in_model neg_in_model pos_in_model  
  by (auto simp add: le_less model_to_dimacs_model_append split: if_splits)

lemma cnf_And: "set (cnf_to_dimacs (f1 \<^bold>\<and> f2)) = set (cnf_to_dimacs f1) \<union> set (cnf_to_dimacs f2)"
  by auto

lemma one_always_in:
  "1 < n_vars \<Longrightarrow> 1 \<in> set (model_to_dimacs_model M ([1..<n_vars])) \<or> - 1 \<in> set (model_to_dimacs_model M ([1..<n_vars]))"
  by (induction n_vars) (auto simp add: less_Suc_eq model_to_dimacs_model_append)

lemma [simp]: "(disj_to_dimacs (f1 \<^bold>\<or> f2)) = (disj_to_dimacs f1) @ (disj_to_dimacs f2)"
  by auto

lemma [simp]: "(atoms (f1 \<^bold>\<or> f2)) = atoms f1 \<union> atoms f2"
  by auto

lemma isdisj_disjD: "(is_disj (f1 \<^bold>\<or> f2)) \<Longrightarrow> is_disj f1 \<and> is_disj f2"
  by (cases f1; auto)

lemma disj_to_dimacs_sound:
   "1 < n_vars \<Longrightarrow> (\<forall>v\<in>atoms f. 0 < v \<and> v < n_vars) \<Longrightarrow> is_disj f \<Longrightarrow> M \<Turnstile> f
     \<Longrightarrow> \<exists>l\<in>set (model_to_dimacs_model M [(1::nat)..<n_vars]). l \<in> set (disj_to_dimacs f)"
  apply(induction f)
  using neg_in_model pos_in_model one_always_in
  by (fastforce elim!: is_lit_plus.elims dest!: isdisj_disjD)+

lemma is_cnf_disj: "is_cnf (f1 \<^bold>\<or> f2) \<Longrightarrow> (\<And>f. f1 \<^bold>\<or> f2 = f \<Longrightarrow> is_disj f \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

lemma cnf_to_dimacs_disj: "is_disj f \<Longrightarrow> cnf_to_dimacs f = [disj_to_dimacs f]"
  by (induction f) auto

lemma model_to_dimacs_model_all_clauses:
  "1 < n_vars \<Longrightarrow> (\<forall>v\<in>atoms f. 0 < v \<and> v < n_vars) \<Longrightarrow> is_cnf f \<Longrightarrow> M \<Turnstile> f \<Longrightarrow>
        c\<in>set (cnf_to_dimacs f) \<Longrightarrow> \<exists>l\<in>set (model_to_dimacs_model M [(1::nat)..<n_vars]). l \<in> set c"
proof(induction f arbitrary: )
  case (Not f)
  then show ?case
    using in_model neg_in_model
    by (fastforce elim!: is_lit_plus.elims)+
next
  case (Or f1 f2)
  then show ?case
    using cnf_to_dimacs_disj disj_to_dimacs_sound
    by(elim is_cnf_disj, simp)
qed (insert in_model neg_in_model pos_in_model, auto)

lemma upt_eq_Cons_conv:
  "(x#xs = [i..<j]) = (i < j \<and> i = x \<and> [i+1..<j] = xs)"
  using upt_eq_Cons_conv
  by metis

lemma model_to_dimacs_model_append':
 "(model_to_dimacs_model M (vs @ vs')) = (model_to_dimacs_model M vs) @ (model_to_dimacs_model M vs')"
  by (induction vs) auto

lemma model_to_dimacs_neg_nin:
 "n_vars \<le> x \<Longrightarrow> int x \<notin> set (model_to_dimacs_model M [a..<n_vars])"
  by (induction n_vars arbitrary: a) (auto simp: model_to_dimacs_model_append')

lemma model_to_dimacs_pos_nin:
 "n_vars \<le> x \<Longrightarrow> - int x \<notin> set (model_to_dimacs_model M [a..<n_vars])"
  by (induction n_vars arbitrary: a) (auto simp: model_to_dimacs_model_append')

lemma int_cases2':
  "z \<noteq> 0 \<Longrightarrow> (\<And>n. 0 \<noteq> (int n) \<Longrightarrow> z = int n \<Longrightarrow> P) \<Longrightarrow> (\<And>n. 0 \<noteq> - (int n) \<Longrightarrow> z = - (int n) \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis (full_types) int_cases2)

lemma model_to_dimacs_model_distinct:
  "1 < n_vars \<Longrightarrow> distinct (map dimacs_lit_to_var (model_to_dimacs_model M [1..<n_vars]))"
  by (induction n_vars)
     (fastforce elim!: int_cases2'
                simp add: dimacs_lit_to_var_def model_to_dimacs_model_append'
                          model_to_dimacs_neg_nin model_to_dimacs_pos_nin)+

lemma model_to_dimacs_model_sound:
  "1 < n_vars \<Longrightarrow> (\<forall>v\<in>atoms f. 0 < v \<and> v < n_vars) \<Longrightarrow> is_cnf f \<Longrightarrow> M \<Turnstile> f \<Longrightarrow>
        dimacs_model (model_to_dimacs_model M [(1::nat)..<n_vars]) (cnf_to_dimacs f)"
  unfolding dimacs_model_def
  using model_to_dimacs_model_all_vars model_to_dimacs_model_all_clauses model_to_dimacs_model_distinct
  by auto  

lemma model_to_dimacs_model_sound_exists:
  "1 < n_vars \<Longrightarrow> (\<forall>v\<in>atoms f. 0 < v \<and> v < n_vars) \<Longrightarrow> is_cnf f \<Longrightarrow> M \<Turnstile> f \<Longrightarrow>
        \<exists>M_dimacs. dimacs_model M_dimacs (cnf_to_dimacs f)"
  using model_to_dimacs_model_sound
  by metis

definition dimacs_to_atom ::"int \<Rightarrow> nat formula" where
  "dimacs_to_atom l \<equiv> if (l < 0) then Not (Atom (nat (abs l))) else Atom (nat (abs l))"

definition dimacs_to_disj::"int list \<Rightarrow> nat formula" where
  "dimacs_to_disj f \<equiv> \<^bold>\<Or> (map dimacs_to_atom f)"

definition dimacs_to_cnf::"int list list \<Rightarrow> nat formula" where
  "dimacs_to_cnf f \<equiv> \<^bold>\<And>map dimacs_to_disj f"

definition "dimacs_model_to_abs dimacs_M M \<equiv> 
  fold (\<lambda>l M. if (l > 0) then M((nat (abs l)):= True) else M((nat (abs l)):= False)) dimacs_M M"

lemma dimacs_model_to_abs_atom:
  "0 < x \<Longrightarrow> int x \<in> set dimacs_M \<Longrightarrow> distinct (map dimacs_lit_to_var  dimacs_M) \<Longrightarrow> dimacs_model_to_abs dimacs_M M x"
proof (induction dimacs_M arbitrary: M rule: rev_induct)
  case (snoc a dimacs_M)
  thus ?case 
    by (auto simp add: dimacs_model_to_abs_def dimacs_lit_to_var_def image_def)
qed auto

lemma dimacs_model_to_abs_atom':
  "0 < x \<Longrightarrow> -(int x) \<in> set dimacs_M \<Longrightarrow> distinct (map dimacs_lit_to_var  dimacs_M) \<Longrightarrow> \<not> dimacs_model_to_abs dimacs_M M x"
proof (induction dimacs_M arbitrary: M rule: rev_induct)
  case (snoc a dimacs_M)
  thus ?case 
    by (auto simp add: dimacs_model_to_abs_def dimacs_lit_to_var_def image_def)
qed auto

lemma model_to_dimacs_model_complete_disj:
  "(\<forall>v\<in>atoms f. 0 < v \<and> v < n_vars) \<Longrightarrow> is_disj f \<Longrightarrow> distinct (map dimacs_lit_to_var dimacs_M)
     \<Longrightarrow> dimacs_model dimacs_M (cnf_to_dimacs f) \<Longrightarrow> dimacs_model_to_abs dimacs_M (\<lambda>_. False) \<Turnstile> f"
  by (induction f)
     (fastforce elim!: is_lit_plus.elims dest!: isdisj_disjD
                simp: cnf_to_dimacs_disj dimacs_model_def dimacs_model_to_abs_atom'
                      dimacs_model_to_abs_atom)+

lemma model_to_dimacs_model_complete:
  "(\<forall>v\<in>atoms f. 0 < v \<and> v < n_vars) \<Longrightarrow> is_cnf f \<Longrightarrow> distinct (map dimacs_lit_to_var dimacs_M)
     \<Longrightarrow> dimacs_model dimacs_M (cnf_to_dimacs f) \<Longrightarrow> dimacs_model_to_abs dimacs_M (\<lambda>_. False) \<Turnstile> f"
proof(induction f)
  case (Not f)
  then show ?case
    by (auto elim!: is_lit_plus.elims simp add: dimacs_model_to_abs_atom' dimacs_model_def)
next
  case (Or f1 f2)
  then show ?case
    using cnf_to_dimacs_disj model_to_dimacs_model_complete_disj
    by(elim is_cnf_disj, simp add: dimacs_model_def)
qed (insert dimacs_model_to_abs_atom, auto simp: dimacs_model_def)

lemma model_to_dimacs_model_complete_max_var:
  "(\<forall>v\<in>atoms f. 0 < v) \<Longrightarrow> is_cnf f \<Longrightarrow> 
   dimacs_model dimacs_M (cnf_to_dimacs f) \<Longrightarrow>
     dimacs_model_to_abs dimacs_M (\<lambda>_. False) \<Turnstile> f"
  using le_imp_less_Suc[OF max_var]
  by (auto intro!: model_to_dimacs_model_complete simp: dimacs_model_def)

lemma model_to_dimacs_model_sound_max_var:
  "(\<forall>v\<in>atoms f. 0 < v) \<Longrightarrow> is_cnf f \<Longrightarrow> M \<Turnstile> f \<Longrightarrow>
     dimacs_model (model_to_dimacs_model M [(1::nat)..<(find_max (formula_vars f) + 2)])
                  (cnf_to_dimacs f)"
  using le_imp_less_Suc[unfolded Suc_eq_plus1, OF max_var]
  by (fastforce intro!: model_to_dimacs_model_sound)

context sat_solve_sasp
begin

lemma [simp]: "var_to_dimacs sv > 0"
  by(cases sv) auto

lemma var_to_dimacs_pos: 
  "v \<in> atoms (map_formula var_to_dimacs f) \<Longrightarrow> 0 < v"
  by (induction f) auto

lemma map_is_disj: "is_disj f \<Longrightarrow> is_disj (map_formula F f)"
  by (induction f) (auto elim: is_lit_plus.elims)

lemma map_is_cnf: "is_cnf f \<Longrightarrow> is_cnf (map_formula F f)"
  by (induction f) (auto elim: is_lit_plus.elims simp: map_is_disj)

lemma planning_dimacs_complete:
  "valid_plan \<pi>s \<Longrightarrow> length \<pi>s \<le> h \<Longrightarrow>
   let cnf_formula = (map_formula var_to_dimacs 
                                  (\<Phi>\<^sub>\<forall> (\<phi> (prob_with_noop abs_prob)) h))
   in
       \<exists>dimacs_M. dimacs_model dimacs_M (cnf_to_dimacs cnf_formula)"
  unfolding Let_def
  by (fastforce simp: var_to_dimacs_pos
                dest!: planning_by_cnf_dimacs_complete
                intro: model_to_dimacs_model_sound_max_var map_is_cnf
                       is_cnf_encode_problem_with_operator_interference_exclusion
                       is_valid_problem_sas_plus_then_strips_transformation_too
                       noops_valid abs_prob_valid)

lemma planning_dimacs_sound:
  "let cnf_formula =
     (map_formula var_to_dimacs
                  (\<Phi>\<^sub>\<forall> (\<phi> (prob_with_noop abs_prob)) h))
   in
     dimacs_model dimacs_M (cnf_to_dimacs cnf_formula) \<Longrightarrow>
   valid_plan 
        (decode_abs_plan
            (rem_noops
              (map (\<lambda>op. \<phi>\<^sub>O\<inverse> (prob_with_noop abs_prob) op)
                   (concat
                    (\<Phi>\<inverse> (\<phi> (prob_with_noop abs_prob)) ((dimacs_model_to_abs dimacs_M (\<lambda>_. False)) o var_to_dimacs) h)))))"
  by(fastforce simp: var_to_dimacs_pos Let_def
               intro: planning_by_cnf_dimacs_sound model_to_dimacs_model_complete_max_var
                      map_is_cnf is_cnf_encode_problem_with_operator_interference_exclusion 
                      is_valid_problem_sas_plus_then_strips_transformation_too abs_prob_valid
                      noops_valid)

end

section \<open>Code Generation\<close>

text \<open>We now generate SML code equivalent to the functions that encode a problem as a CNF formula
      and that decode the model of the given encodings into a plan.\<close>

lemma [code]:
   "dimacs_model ls cs \<equiv> (list_all (\<lambda>c. list_ex (\<lambda>l. ListMem l c ) ls) cs) \<and>
                               distinct (map dimacs_lit_to_var ls)"
  unfolding dimacs_model_def
  by (auto simp: list.pred_set ListMem_iff list_ex_iff )

definition 
"SASP_to_DIMACS h prob \<equiv>
   cnf_to_dimacs
     (map_formula 
       (cnf_to_dimacs.var_to_dimacs (Suc h) (Suc (length (ast_problem.ast\<delta> prob))))
         (\<Phi>\<^sub>\<forall> (\<phi> (prob_with_noop (ast_problem.abs_prob prob))) h))"

lemma planning_dimacs_complete_code:
  "\<lbrakk>ast_problem.well_formed prob;
    \<forall>\<pi>\<in>set (ast_problem.ast\<delta> prob). is_standard_operator' \<pi>;
    ast_problem.valid_plan prob \<pi>s;
    length \<pi>s \<le> h\<rbrakk> \<Longrightarrow>
   let cnf_formula = (SASP_to_DIMACS h prob) in
       \<exists>dimacs_M. dimacs_model dimacs_M cnf_formula"
  unfolding SASP_to_DIMACS_def Let_def
  apply(rule sat_solve_sasp.planning_dimacs_complete[unfolded Let_def])
  apply unfold_locales
  by auto

definition "SASP_to_DIMACS' h prob \<equiv> SASP_to_DIMACS h (rem_implicit_pres_ops prob)"

lemma planning_dimacs_complete_code':
  "\<lbrakk>ast_problem.well_formed prob;
    (\<And>op. op \<in> set (ast_problem.ast\<delta> prob) \<Longrightarrow> consistent_pres_op op);
    (\<And>op. op \<in> set (ast_problem.ast\<delta> prob) \<Longrightarrow> is_standard_operator op);
    ast_problem.valid_plan prob \<pi>s;
    length \<pi>s \<le> h\<rbrakk> \<Longrightarrow>
   let cnf_formula = (SASP_to_DIMACS' h prob) in
       \<exists>dimacs_M. dimacs_model dimacs_M cnf_formula"
  unfolding Let_def SASP_to_DIMACS'_def
  by (auto simp add: rem_implicit_pres_ops_valid_plan[symmetric] wf_ast_problem_def
           simp del: rem_implicit_pres.simps
           intro!: rem_implicit_pres_is_standard_operator'
                   planning_dimacs_complete_code[unfolded Let_def]
                   rem_implicit_pres_ops_well_formed
           dest!: rem_implicit_pres_ops_in\<delta>D)

text \<open>A function that does the checks required by the completeness theorem above, and returns
      appropriate error messages if any of the checks fail.\<close>

definition
  "encode h prob \<equiv>
     if ast_problem.well_formed prob then
       if (\<forall>op \<in> set (ast_problem.ast\<delta> prob). consistent_pres_op op) then
         if (\<forall>op \<in> set (ast_problem.ast\<delta> prob). is_standard_operator op) then
           Inl (SASP_to_DIMACS' h prob)
         else
           Inr (STR ''Error: Conditional effects!'')
       else
         Inr (STR ''Error: Preconditions inconsistent'')
     else
       Inr (STR ''Error: Problem malformed!'')"

lemma encode_sound:
  "\<lbrakk>ast_problem.valid_plan prob \<pi>s; length \<pi>s \<le> h;
        encode h prob = Inl cnf_formula\<rbrakk> \<Longrightarrow> 
         (\<exists>dimacs_M. dimacs_model dimacs_M cnf_formula)"
  unfolding encode_def
  by (auto split: if_splits simp: list.pred_set
           intro: planning_dimacs_complete_code'[unfolded Let_def])

lemma encode_complete:
  "encode h prob = Inr err \<Longrightarrow> 
     \<not>(ast_problem.well_formed prob \<and> (\<forall>op \<in> set (ast_problem.ast\<delta> prob). consistent_pres_op op) \<and>
     (\<forall>op \<in> set (ast_problem.ast\<delta> prob). is_standard_operator op))"
  unfolding encode_def
  by (auto split: if_splits simp: list.pred_set
           intro: planning_dimacs_complete_code'[unfolded Let_def])

definition match_pre where
    "match_pre \<equiv> \<lambda>(x,v) s. s x = Some v"
    
definition match_pres where 
    "match_pres pres s \<equiv> \<forall>pre\<in>set pres. match_pre pre s"

lemma match_pres_distinct: 
  "distinct (map fst pres) \<Longrightarrow> match_pres pres s \<longleftrightarrow> Map.map_of pres \<subseteq>\<^sub>m s"
  unfolding match_pres_def match_pre_def 
  using map_le_def map_of_SomeD
  apply (auto split: prod.splits)
   apply fastforce
  using domI map_of_is_SomeI
  by smt

fun tree_map_of where
  "tree_map_of updatea T [] = T"
| "tree_map_of updatea T ((v,a)#m) = updatea v a (tree_map_of updatea T m)"

context Map
begin

abbreviation "tree_map_of' \<equiv> tree_map_of update"

lemma tree_map_of_invar: "invar T \<Longrightarrow> invar (tree_map_of' T pres)"
  by (induction pres) (auto simp add: invar_update)

lemma tree_map_of_works: "lookup (tree_map_of' empty pres) x = map_of pres x"
  by (induction pres) (auto simp: map_empty map_update[OF tree_map_of_invar[OF invar_empty]])

lemma tree_map_of_dom: "dom (lookup (tree_map_of' empty pres)) = dom (map_of pres)"
  by (induction pres) (auto simp: map_empty map_update[OF tree_map_of_invar[OF invar_empty]] tree_map_of_works)
end

lemma distinct_if_sorted: "sorted xs \<Longrightarrow> distinct xs"
  by (induction xs rule: induct_list012) auto

context Map_by_Ordered
begin

lemma tree_map_of_distinct: "distinct (map fst (inorder (tree_map_of' empty pres)))"
  apply(induction pres) 
   apply(clarsimp simp: map_empty inorder_empty)
  using distinct_if_sorted invar_def invar_empty invar_update tree_map_of_invar
  by blast

end

lemma set_tree_intorder: "set_tree t = set (inorder t)"
  by (induction t) auto

lemma map_of_eq:
  "map_of xs = Map.map_of xs"
  by (induction xs) (auto simp: map_of_simps split: option.split)

lemma lookup_someD: "lookup T x = Some y \<Longrightarrow> \<exists>p. p \<in> set (inorder T) \<and> p = (x, y)"
  by (induction T) (auto split: if_splits)

lemma map_of_lookup: "sorted1 (inorder T) \<Longrightarrow> Map.map_of (inorder T) = lookup T"
  apply(induction T)
   apply (auto split: prod.splits intro!: map_le_antisym
      simp: lookup_map_of map_add_Some_iff map_of_None2 sorted_wrt_append)
  using lookup_someD
  by (force simp: map_of_eq map_add_def map_le_def
            split: option.splits)+

lemma map_le_cong: "(\<And>x. m1 x = m2 x) \<Longrightarrow> m1 \<subseteq>\<^sub>m s \<longleftrightarrow> m2 \<subseteq>\<^sub>m s"
  by presburger

lemma match_pres_submap:
  "match_pres (inorder (M.tree_map_of' empty pres)) s \<longleftrightarrow> Map.map_of pres \<subseteq>\<^sub>m s"
  using match_pres_distinct[OF M.tree_map_of_distinct]
  by (smt M.invar_def M.invar_empty M.tree_map_of_invar M.tree_map_of_works map_le_cong map_of_eq map_of_lookup)  

lemma [code]:
  "SAS_Plus_Representation.is_operator_applicable_in s op \<longleftrightarrow> 
      match_pres (inorder (M.tree_map_of' empty (SAS_Plus_Representation.precondition_of op))) s"
  by (simp add: match_pres_submap SAS_Plus_Representation.is_operator_applicable_in_def)

definition "decode_DIMACS_model dimacs_M h prob \<equiv> 
  (ast_problem.decode_abs_plan prob
      (rem_noops
         (map (\<lambda>op. \<phi>\<^sub>O\<inverse> (prob_with_noop (ast_problem.abs_prob prob)) op)
           (concat 
              (\<Phi>\<inverse> (\<phi> (prob_with_noop (ast_problem.abs_prob prob)))
                   ((dimacs_model_to_abs dimacs_M (\<lambda>_. False)) o
                     (cnf_to_dimacs.var_to_dimacs (Suc h)
                        (Suc (length (ast_problem.ast\<delta> prob)))))
                   h)))))"

lemma planning_dimacs_sound_code:
  "\<lbrakk>ast_problem.well_formed prob;
    \<forall>\<pi>\<in>set (ast_problem.ast\<delta> prob). is_standard_operator' \<pi>\<rbrakk> \<Longrightarrow>
    let
      cnf_formula = (SASP_to_DIMACS h prob);
      decoded_plan = decode_DIMACS_model dimacs_M h prob
    in
     (dimacs_model dimacs_M cnf_formula \<longrightarrow> ast_problem.valid_plan prob decoded_plan)"
  unfolding SASP_to_DIMACS_def decode_DIMACS_model_def Let_def
  apply(rule impI sat_solve_sasp.planning_dimacs_sound[unfolded Let_def])+
  apply unfold_locales
  by auto

definition
  "decode_DIMACS_model' dimacs_M h prob \<equiv> 
     decode_DIMACS_model dimacs_M h (rem_implicit_pres_ops prob)"

lemma planning_dimacs_sound_code':
  "\<lbrakk>ast_problem.well_formed prob;
   (\<And>op. op \<in> set (ast_problem.ast\<delta> prob) \<Longrightarrow> consistent_pres_op op);
    \<forall>\<pi>\<in>set (ast_problem.ast\<delta> prob). is_standard_operator \<pi>\<rbrakk> \<Longrightarrow>
    let
      cnf_formula = (SASP_to_DIMACS' h prob);
      decoded_plan = decode_DIMACS_model' dimacs_M h prob
    in
     (dimacs_model dimacs_M cnf_formula \<longrightarrow> ast_problem.valid_plan prob decoded_plan)"
  unfolding SASP_to_DIMACS'_def decode_DIMACS_model'_def
  apply(subst rem_implicit_pres_ops_valid_plan[symmetric])
  by(fastforce simp only: rem_implicit_pres_ops_valid_plan wf_ast_problem_def
           intro!: rem_implicit_pres_is_standard_operator'
                   rem_implicit_pres_ops_well_formed
                   rev_iffD2[OF _ rem_implicit_pres_ops_valid_plan]
                   planning_dimacs_sound_code wf_ast_problem.intro
           dest!: rem_implicit_pres_ops_in\<delta>D)+

text \<open>Checking if the model satisfies the formula takes the longest time in the decoding function.
      We reimplement that part using red black trees, which makes it 10 times faster, on average!\<close>

fun list_to_rbt :: "int list \<Rightarrow> int rbt" where
  "list_to_rbt [] = Leaf"
| "list_to_rbt (x#xs) = insert_rbt x (list_to_rbt xs)"

lemma inv_list_to_rbt: "invc (list_to_rbt xs) \<and> invh (list_to_rbt xs)"
  by (induction xs) (auto simp: rbt_def RBT.inv_insert)

lemma Tree2_list_to_rbt: "Tree2.bst (list_to_rbt xs)"
  by (induction xs) (auto simp: RBT.bst_insert)

lemma set_list_to_rbt: "Tree2.set_tree (list_to_rbt xs) = set xs"
  by (induction xs) (simp add: RBT.set_tree_insert Tree2_list_to_rbt)+

text \<open>The following \<close>

lemma dimacs_model_code[code]:
  "dimacs_model ls cs \<longleftrightarrow> 
        (let tls = list_to_rbt ls in
          (\<forall>c\<in>set cs. size (inter_rbt (tls) (list_to_rbt c)) \<noteq> 0) \<and>
               distinct (map dimacs_lit_to_var ls))"
  using RBT.set_tree_inter[OF Tree2_list_to_rbt Tree2_list_to_rbt]
  apply (auto simp: dimacs_model_def Let_def set_list_to_rbt inter_rbt_def)
  apply (metis IntI RBT.set_empty empty_iff)
  by (metis Tree2.eq_set_tree_empty disjoint_iff_not_equal)

definition
  "decode M h prob \<equiv>
     if ast_problem.well_formed prob then
       if (\<forall>op\<in>set (ast_problem.ast\<delta> prob). consistent_pres_op op) then
         if (\<forall>op\<in>set (ast_problem.ast\<delta> prob). is_standard_operator op) then
           if (dimacs_model M (SASP_to_DIMACS' h prob)) then
             Inl (decode_DIMACS_model' M h prob)
           else Inr (STR ''Error: Model does not solve the problem!'')
         else
           Inr (STR ''Error: Conditional effects!'')
       else
         Inr (STR ''Error: Preconditions inconsistent'')
     else
       Inr (STR ''Error: Problem malformed!'')"

lemma decode_sound:
  "decode M h prob = Inl plan \<Longrightarrow> 
         ast_problem.valid_plan prob plan"
  unfolding decode_def
  apply (auto split: if_splits simp: list.pred_set)
  using planning_dimacs_sound_code'
  by auto

lemma decode_complete:
  "decode M h prob = Inr err \<Longrightarrow>
         \<not> (ast_problem.well_formed prob \<and> 
            (\<forall>op \<in> set (ast_problem.ast\<delta> prob). consistent_pres_op op) \<and>
            (\<forall>\<pi>\<in>set (ast_problem.ast\<delta> prob). is_standard_operator \<pi>) \<and> 
            dimacs_model M (SASP_to_DIMACS' h prob))"
  unfolding decode_def
  by (auto split: if_splits simp: list.pred_set)

lemma [code]:
  "ListMem x' []= False"
  "ListMem x' (x#xs) = (x' = x \<or> ListMem x' xs)"
  by (simp add: ListMem_iff)+

lemmas [code] = SASP_to_DIMACS_def ast_problem.abs_prob_def
                ast_problem.abs_ast_variable_section_def ast_problem.abs_ast_operator_section_def
                ast_problem.abs_ast_initial_state_def ast_problem.abs_range_map_def
                ast_problem.abs_ast_goal_def cnf_to_dimacs.var_to_dimacs.simps
                ast_problem.ast\<delta>_def ast_problem.astDom_def ast_problem.abs_ast_operator_def
                ast_problem.astI_def ast_problem.astG_def ast_problem.lookup_action_def
                ast_problem.I_def execute_operator_sas_plus_def ast_problem.decode_abs_plan_def

definition nat_opt_of_integer :: "integer \<Rightarrow> nat option" where
       "nat_opt_of_integer i = (if (i \<ge> 0) then Some (nat_of_integer i) else None)"

definition max_var :: "int list \<Rightarrow> int" where
       "max_var xs \<equiv> fold (\<lambda>(x::int) (y::int). if abs x \<ge> abs y then (abs x) else y) xs (0::int)"

export_code encode nat_of_integer integer_of_nat nat_opt_of_integer Inl Inr String.explode
    String.implode max_var concat char_of_nat Int.nat integer_of_int length int_of_integer
  in SML module_name exported file_prefix SASP_to_DIMACS

export_code decode nat_of_integer integer_of_nat nat_opt_of_integer Inl Inr String.explode
    String.implode max_var concat char_of_nat Int.nat integer_of_int length int_of_integer
  in SML module_name exported file_prefix decode_DIMACS_model

end
