section\<open>Code Generation\<close>
text\<open>This theory is used to generate an executable Scala implementation of the inference tool which
can be used to infer real EFSMs from real traces. Certain functions are replaced with native
implementations. These can be found at \url{https://github.com/jmafoster1/efsm-inference/blob/master/inference-tool/src/main/scala/inference/Dirties.scala}.\<close>

theory Code_Generation
  imports
   "HOL-Library.Code_Target_Numeral"
   Inference
   SelectionStrategies
   "heuristics/Store_Reuse_Subsumption"
   "heuristics/Increment_Reset"
   "heuristics/Same_Register"
   "heuristics/Distinguishing_Guards"
   "heuristics/PTA_Generalisation"
   "heuristics/Weak_Subsumption"
   "heuristics/Least_Upper_Bound"
   EFSM_Dot
   "code-targets/Code_Target_FSet"
   "code-targets/Code_Target_Set"
   "code-targets/Code_Target_List"
efsm2sal
begin

declare One_nat_def [simp del]

(*
  Let's use the native operators for booleans and pairs
*)
code_printing
  constant HOL.conj \<rightharpoonup> (Scala) "_ && _" |
  constant HOL.disj \<rightharpoonup> (Scala) "_ || _" |
  constant "HOL.equal :: bool \<Rightarrow> bool \<Rightarrow> bool" \<rightharpoonup> (Scala) infix 4 "==" |
  constant "fst" \<rightharpoonup> (Scala) "_.'_1" |
  constant "snd" \<rightharpoonup> (Scala) "_.'_2"|
  constant "(1::nat)" \<rightharpoonup> (Scala) "Nat.Nata((1))"

(*
  This gives us a speedup as we don't need to check that a register is undefined in the initial
  state if there is no way to get back there. This is true by definition.
*)
definition "initially_undefined_context_check_full = initially_undefined_context_check"

(* This gives us a speedup because we can check this before we have to call out to z3 *)
fun mutex :: "'a gexp \<Rightarrow> 'a gexp \<Rightarrow> bool" where
  "mutex (Eq (V v) (L l)) (Eq (V v') (L l')) = (if v = v' then l \<noteq> l' else False)" |
  "mutex (gexp.In v l) (Eq (V v') (L l')) = (v = v' \<and> l' \<notin> set l)" |
  "mutex (Eq (V v') (L l')) (gexp.In v l) = (v = v' \<and> l' \<notin> set l)" |
  "mutex (gexp.In v l) (gexp.In v' l') = (v = v' \<and> set l \<inter> set l' = {})" |
  "mutex _ _ = False"

lemma mutex_not_gval:
  "mutex x y \<Longrightarrow> gval (gAnd y x) s \<noteq> true"
  unfolding gAnd_def
  apply (induct x y rule: mutex.induct)
                      apply simp_all
     apply (case_tac "s v")
      apply (case_tac "s v'")
       apply simp
      apply simp
     apply (case_tac "s v")
      apply (case_tac "s v'")
       apply simp
      apply simp
     apply (metis maybe_negate_true maybe_or_false trilean.distinct(1) value_eq.simps(3))
    apply (case_tac "s v")
     apply (case_tac "s v'")
      apply simp
     apply simp
    apply simp
    apply (case_tac "s v'")
     apply simp
    apply simp
   apply (case_tac "s v")
     apply (case_tac "s v'")
  by auto

(* (\<exists>(i, s1) \<in> set (get_ins (Guard t1)).
   \<exists>(i', s2) \<in> set (get_ins (Guard t2)).
   i = i' \<and>
   \<not> (set s2) \<subseteq> (set s1) \<and>
   restricted_once (I i) (Guard t2)) *)

definition choice_cases :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "choice_cases t1 t2 = (
     if \<exists>(x, y) \<in> set (List.product (Guards t1) (Guards t2)). mutex x y then
       False
     else if Guards t1 = Guards t2 then
       satisfiable (fold gAnd (rev (Guards t1)) (gexp.Bc True))
     else
       satisfiable ((fold gAnd (rev (Guards t1@Guards t2)) (gexp.Bc True)))
   )"

lemma existing_mutex_not_true:
  "\<exists>x\<in>set G. \<exists>y\<in>set G. mutex x y \<Longrightarrow> \<not> apply_guards G s"
  apply clarify
  apply (simp add: apply_guards_rearrange)
  apply (case_tac "y \<in> set (x#G)")
   defer
   apply simp
  apply (simp only: apply_guards_rearrange)
  apply simp
  apply (simp only: apply_guards_double_cons)
  using mutex_not_gval
  by auto

lemma [code]: "choice t t' = choice_cases t t'"
  apply (simp only: choice_alt choice_cases_def)
  apply (case_tac "\<exists>x\<in>set (map (\<lambda>(x, y). mutex x y) (List.product (Guards t) (Guards t'))). x")
   apply (simp add: choice_alt_def)
   apply (metis existing_mutex_not_true Un_iff set_append)
  apply (case_tac "Guards t = Guards t'")
   apply (simp add: choice_alt_def apply_guards_append)
   apply (simp add: fold_apply_guards rev_apply_guards satisfiable_def)
  apply (simp add: choice_alt_def satisfiable_def)
  by (metis foldr_append foldr_apply_guards foldr_conv_fold)

fun guardMatch_code :: "vname gexp list \<Rightarrow> vname gexp list \<Rightarrow> bool" where
  "guardMatch_code [(gexp.Eq (V (vname.I i)) (L (Num n)))] [(gexp.Eq (V (vname.I i')) (L (Num n')))] = (i = 0 \<and> i' = 0)" |
  "guardMatch_code _ _ = False"

lemma [code]: "guardMatch t1 t2 = guardMatch_code (Guards t1) (Guards t2)"
  apply (simp add: guardMatch_def)
  using guardMatch_code.elims(2) by fastforce

fun outputMatch_code :: "output_function list \<Rightarrow> output_function list \<Rightarrow> bool" where
  "outputMatch_code [L (Num n)] [L (Num n')] = True" |
  "outputMatch_code _ _ = False"

lemma [code]: "outputMatch t1 t2 = outputMatch_code (Outputs t1) (Outputs t2)"
  by (metis outputMatch_code.elims(2) outputMatch_code.simps(1) outputMatch_def)

fun always_different_outputs :: "vname aexp list \<Rightarrow> vname aexp list \<Rightarrow> bool" where
  "always_different_outputs [] [] = False" |
  "always_different_outputs [] (a#_) = True" |
  "always_different_outputs (a#_) [] = True" |
  "always_different_outputs ((L v)#t) ((L v')#t') = (if v = v' then always_different_outputs t t' else True)" |
  "always_different_outputs (h#t) (h'#t') = always_different_outputs t t'"

lemma always_different_outputs_outputs_never_equal:
  "always_different_outputs O1 O2 \<Longrightarrow>
   apply_outputs O1 s \<noteq> apply_outputs O2 s"
  apply(induct O1 O2 rule: always_different_outputs.induct)
  by (simp_all add: apply_outputs_def)

fun tests_input_equality :: "nat \<Rightarrow> vname gexp \<Rightarrow> bool" where
  "tests_input_equality i (gexp.Eq (V (vname.I i')) (L _)) = (i = i')" |
  "tests_input_equality _ _ = False"

fun no_illegal_updates_code :: "update_function list \<Rightarrow> nat \<Rightarrow> bool" where
  "no_illegal_updates_code [] _ = True" |
  "no_illegal_updates_code ((r', u)#t) r = (r \<noteq> r' \<and> no_illegal_updates_code t r)"

lemma no_illegal_updates_code_aux:
  "(\<forall>u\<in>set u. fst u \<noteq> r) = no_illegal_updates_code u r"
proof(induct u)
case Nil
  then show ?case
    by simp
next
case (Cons a u)
  then show ?case
    apply (cases a)
    apply (case_tac aa)
    by auto
qed

lemma no_illegal_updates_code [code]:
  "no_illegal_updates t r = no_illegal_updates_code (Updates t) r"
  by (simp add: no_illegal_updates_def no_illegal_updates_code_aux)

fun input_updates_register_aux :: "update_function list \<Rightarrow> nat option" where
  "input_updates_register_aux ((n, V (vname.I n'))#_) = Some n'" |
  "input_updates_register_aux (h#t) = input_updates_register_aux t" |
  "input_updates_register_aux [] = None"

definition input_updates_register :: "transition_matrix \<Rightarrow> (nat \<times> String.literal)" where
  "input_updates_register e = (
    case fthe_elem (ffilter (\<lambda>(_, t). input_updates_register_aux (Updates t) \<noteq> None) e) of
      (_, t) \<Rightarrow> (case
        input_updates_register_aux (Updates t) of
          Some n \<Rightarrow> (n, Label t)
      )
  )"

definition "dirty_directly_subsumes e1 e2 s1 s2 t1 t2 = (if t1 = t2 then True else directly_subsumes e1 e2 s1 s2 t1 t2)"

definition "always_different_outputs_direct_subsumption m1 m2 s s' t2 = ((\<exists>p c1 c. obtains s c1 m1 0 <> p \<and> obtains s' c m2 0 <> p \<and> (\<exists>i. can_take_transition t2 i c)))"

lemma always_different_outputs_direct_subsumption:
  "always_different_outputs (Outputs t1) (Outputs t2) \<Longrightarrow>
   always_different_outputs_direct_subsumption m1 m2 s s' t2 \<Longrightarrow>
   \<not> directly_subsumes m1 m2 s s' t1 t2"
  apply (simp add: directly_subsumes_def always_different_outputs_direct_subsumption_def)
  apply (erule exE)
  apply (erule conjE)
  apply (erule exE)+
  apply (rule_tac x=c1 in exI)
  apply (rule_tac x=c in exI)
  by (metis always_different_outputs_outputs_never_equal bad_outputs)

definition negate :: "'a gexp list \<Rightarrow> 'a gexp" where
  "negate g = gNot (fold gAnd g (Bc True))"

lemma gval_negate_cons:
  "gval (negate (a # G)) s = gval (gNot a) s \<or>? gval (negate G) s"
  apply (simp only: negate_def gval_gNot gval_fold_equiv_gval_foldr)
  by (simp only: foldr.simps comp_def gval_gAnd de_morgans_2)

lemma negate_true_guard:
  "(gval (negate G) s = true) = (gval (fold gAnd G (Bc True)) s = false)"
  by (metis (no_types, lifting) gval_gNot maybe_double_negation maybe_not.simps(1) negate_def)

lemma gval_negate_not_invalid:
  "(gval (negate gs) (join_ir i ra) \<noteq> invalid) = (gval (fold gAnd gs (Bc True)) (join_ir i ra) \<noteq> invalid)"
  by (metis gval_gNot maybe_not_invalid negate_def)

definition "dirty_always_different_outputs_direct_subsumption = always_different_outputs_direct_subsumption"

lemma [code]: "always_different_outputs_direct_subsumption m1 m2 s s' t = (
  if Guards t = [] then
    recognises_and_visits_both m1 m2 s s'
  else
    dirty_always_different_outputs_direct_subsumption m1 m2 s s' t
  )"
  apply (simp add: always_different_outputs_direct_subsumption_def)
  apply (simp add: recognises_and_visits_both_def)
  apply safe
     apply (rule_tac x=p in exI)
     apply auto[1]
  using can_take_transition_empty_guard apply blast
  apply (metis always_different_outputs_direct_subsumption_def dirty_always_different_outputs_direct_subsumption_def)
  by (simp add: always_different_outputs_direct_subsumption_def dirty_always_different_outputs_direct_subsumption_def)

definition guard_subset_subsumption :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "guard_subset_subsumption t1 t2 = (Label t1 = Label t2 \<and> Arity t1 = Arity t2 \<and> set (Guards t1) \<subseteq> set (Guards t2) \<and> Outputs t1 = Outputs t2 \<and> Updates t1 = Updates t2)"

lemma guard_subset_subsumption:
  "guard_subset_subsumption t1 t2 \<Longrightarrow> directly_subsumes a b s s' t1 t2"
  apply (rule subsumes_in_all_contexts_directly_subsumes)
  apply (simp add: subsumes_def guard_subset_subsumption_def)
  by (metis can_take_def can_take_transition_def can_take_subset)

definition "guard_subset_eq_outputs_updates t1 t2 = (Label t1 = Label t2 \<and>
   Arity t1 = Arity t2 \<and>
   Outputs t1 = Outputs t2 \<and>
   Updates t1 = Updates t2 \<and>
   set (Guards t2) \<subseteq> set (Guards t1))"

definition "guard_superset_eq_outputs_updates t1 t2 = (Label t1 = Label t2 \<and>
   Arity t1 = Arity t2 \<and>
   Outputs t1 = Outputs t2 \<and>
   Updates t1 = Updates t2 \<and>
   set (Guards t2) \<supset> set (Guards t1))"

definition is_generalisation_of :: "transition \<Rightarrow> transition \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "is_generalisation_of t' t i r = (
    t' = remove_guard_add_update t i r \<and>
    i < Arity t \<and>
    r \<notin> set (map fst (Updates t)) \<and>
    (length (filter (tests_input_equality i) (Guards t)) \<ge> 1)
  )"

lemma tests_input_equality:
  "(\<exists>v. gexp.Eq (V (vname.I xb)) (L v) \<in> set G) = (1 \<le> length (filter (tests_input_equality xb) G))"
proof(induct G)
  case Nil
  then show ?case by simp
next
  case (Cons a G)
  then show ?case
    apply (cases a)
        apply simp
       apply simp
       apply (case_tac x21)
          apply simp
         apply simp
         apply (case_tac "x2 = vname.I xb")
          apply simp
          defer
          defer
          apply simp+
     apply (case_tac x22)
        apply auto[1]
       apply simp+
    apply (case_tac x22)
    using tests_input_equality.elims(2) by auto
qed

lemma [code]:
  "Store_Reuse.is_generalisation_of x xa xb xc = is_generalisation_of x xa xb xc"
  apply (simp add: Store_Reuse.is_generalisation_of_def is_generalisation_of_def)
  using tests_input_equality by blast

definition iEFSM2dot :: "iEFSM \<Rightarrow> nat \<Rightarrow> unit" where
  "iEFSM2dot _ _ = ()"

definition logStates :: "iEFSM \<Rightarrow> nat \<Rightarrow> unit" where
  "logStates _ _ = ()"

(* This is the infer function but with logging *)
(*
function infer_with_log :: "nat \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> strategy \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM" where
  "infer_with_log stepNo k e r m check np = (
    let scores = if k = 1 then score_1 e r else (k_score k e r) in
    case inference_step e scores m check np of
      None \<Rightarrow> e |
      Some new \<Rightarrow> let
        temp = iEFSM2dot new stepNo;
        temp2 = logStates (size (S new)) (size (S e)) in
        if (S new) |\<subset>| (S e) then
          infer_with_log (stepNo + 1) k new r m check np
        else e
  )"
*)

(*
function infer_with_log :: "(cfstate \<times> cfstate) set \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> strategy \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM" where *)

function infer_with_log :: "(cfstate \<times> cfstate) set \<Rightarrow> nat \<Rightarrow> iEFSM \<Rightarrow> strategy \<Rightarrow> update_modifier \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> (iEFSM \<Rightarrow> nondeterministic_pair fset) \<Rightarrow> iEFSM" where
  "infer_with_log failedMerges k e r m check np = (
    let scores = if k = 1 then score_1 e r else (k_score k e r) in
    case inference_step failedMerges e (ffilter (\<lambda>s. (S1 s, S2 s) \<notin> failedMerges \<and> (S2 s, S1 s) \<notin> failedMerges) scores) m check np of
      (None, _) \<Rightarrow> e |
      (Some new, failedMerges) \<Rightarrow> if (Inference.S new) |\<subset>| (Inference.S e) then
      let temp2 = logStates new (size (Inference.S e)) in
      infer_with_log failedMerges k new r m check np else e
  )"
  by auto
termination
  apply (relation "measures [\<lambda>(_, _, e, _). size (Inference.S e)]")
   apply simp
  by (metis (no_types, lifting) case_prod_conv measures_less size_fsubset)

lemma infer_empty: "infer f k {||} r m check np = {||}"
  by (simp add: score_1_def S_def fprod_empty k_score_def)

(*
lemma [code]: "infer f k e r m check np = infer_with_log f k e r m check np"
  sorry
*)

(* declare make_pta_fold [code] *)
declare GExp.satisfiable_def [code del]
declare initially_undefined_context_check_full_def [code del]
declare generalise_output_context_check_def [code del]
declare dirty_always_different_outputs_direct_subsumption_def [code del]
declare diff_outputs_ctx_def [code del]
declare random_member_def [code del]
declare dirty_directly_subsumes_def [code del]
declare recognises_and_visits_both_def [code del]
declare initially_undefined_context_check_def [code del]
declare can_still_take_ctx_def [code del]

code_printing
  constant infer \<rightharpoonup> (Scala) "Code'_Generation.infer'_with'_log" |
  constant recognises_and_visits_both \<rightharpoonup> (Scala) "Dirties.recognisesAndGetsUsToBoth" |
  constant iEFSM2dot \<rightharpoonup> (Scala) "PrettyPrinter.iEFSM2dot(_, _)" |
  constant logStates \<rightharpoonup> (Scala) "Log.logStates(_, _)" |
  constant "dirty_directly_subsumes" \<rightharpoonup> (Scala) "Dirties.scalaDirectlySubsumes" |
  constant "GExp.satisfiable" \<rightharpoonup> (Scala) "Dirties.satisfiable" |
  constant "initially_undefined_context_check_full" \<rightharpoonup> (Scala) "Dirties.initiallyUndefinedContextCheck" |
  constant "generalise_output_context_check" \<rightharpoonup> (Scala) "Dirties.generaliseOutputContextCheck" |
  constant "dirty_always_different_outputs_direct_subsumption" \<rightharpoonup> (Scala) "Dirties.alwaysDifferentOutputsDirectSubsumption" |
  constant "diff_outputs_ctx" \<rightharpoonup> (Scala) "Dirties.diffOutputsCtx" |
  constant "can_still_take" \<rightharpoonup> (Scala) "Dirties.canStillTake" |
  constant "random_member" \<rightharpoonup> (Scala) "Dirties.randomMember"

code_printing
  constant "show_nat" \<rightharpoonup> (Scala) "Code'_Numeral.integer'_of'_nat((_)).toString()"
  | constant "show_int" \<rightharpoonup> (Scala) "Code'_Numeral.integer'_of'_int((_)).toString()"
  | constant "join" \<rightharpoonup> (Scala) "_.mkString((_))"

(*
  Mapping finfuns to Scala native Maps
*)
code_printing
  type_constructor finfun \<rightharpoonup> (Scala) "Map[_, _]"
  | constant "finfun_const" \<rightharpoonup> (Scala) "scala.collection.immutable.Map().withDefaultValue((_))"
  | constant "finfun_update" \<rightharpoonup> (Scala) "_ + (_ -> _)"
  | constant "finfun_apply" \<rightharpoonup> (Scala) "_((_))"
  | constant "finfun_to_list" \<rightharpoonup> (Scala) "_.keySet.toList"
declare finfun_to_list_const_code [code del]
declare finfun_to_list_update_code [code del]

definition mismatched_updates :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "mismatched_updates t1 t2 = (\<exists>r \<in> set (map fst (Updates t1)). r \<notin> set (map fst (Updates t2)))"

lemma [code]:
  "directly_subsumes e1 e2 s1 s2 t1 t2  = (if t1 = t2 then True else dirty_directly_subsumes e1 e2 s1 s2 t1 t2)"
  by (simp add: directly_subsumes_reflexive dirty_directly_subsumes_def)

export_code
  (* Essentials *)
  try_heuristics_check
  learn
  infer_with_log
  nondeterministic
  make_pta
  AExp.enumerate_vars
  (* Logical connectives *)
  gAnd
  gOr
  gNot
  Lt
  Le
  Ge
  Ne
  (* Scoring functions *)
  naive_score
  naive_score_eq_bonus
  exactly_equal
  naive_score_outputs
  naive_score_comprehensive
  naive_score_comprehensive_eq_high
  leaves
  (* Heuristics *)
  same_register
  insert_increment_2
  heuristic_1
  heuristic_2
  distinguish
  weak_subsumption
  lob
  (* Nondeterminism metrics *)
  nondeterministic_pairs
  nondeterministic_pairs_labar
  nondeterministic_pairs_labar_dest
  (* Utilities *)
  min
  max
  drop_pta_guards
  test_log
  iefsm2dot
  efsm2dot
  guards2sal
  guards2sal_num
  fold_In
  max_int
  enumerate_vars
  derestrict
in Scala
(* file "../../inference-tool/src/main/scala/inference/Inference.scala" *)

end
