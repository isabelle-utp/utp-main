section\<open>Distinguishing Guards\<close>
text\<open>If we cannot resolve the nondeterminism which arises from merging states by merging
transitions, we might then conclude that those states should not be merged. Alternatively, we could
consider the possibility of \emph{value-dependent} behaviour. This theory presents a heuristic which
tries to find a guard which distinguishes between a pair of transitions.\<close>

theory Distinguishing_Guards
imports "../Inference"
begin

hide_const uids

definition put_updates :: "tids \<Rightarrow> update_function list \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "put_updates uids updates iefsm = fimage (\<lambda>(uid, fromTo, tran).
      case uid of [u] \<Rightarrow>
      if u \<in> set uids then
        (uid, fromTo, \<lparr>Label = Label tran, Arity = Arity tran, Guards = Guards tran, Outputs = Outputs tran, Updates = (Updates tran)@updates\<rparr>)
      else
        (uid, fromTo, tran)
      ) iefsm"

definition transfer_updates :: "iEFSM \<Rightarrow> iEFSM \<Rightarrow> iEFSM" where
  "transfer_updates e pta = fold (\<lambda>(tids, (from, to), tran) acc. put_updates tids (Updates tran) acc) (sorted_list_of_fset e) pta"

fun trace_collect_training_sets :: "trace \<Rightarrow> iEFSM \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> tids \<Rightarrow> tids \<Rightarrow> (inputs \<times> registers) list \<Rightarrow> (inputs \<times> registers) list \<Rightarrow> ((inputs \<times> registers) list \<times> (inputs \<times> registers) list)" where
  "trace_collect_training_sets [] uPTA s registers T1 T2 G1 G2 = (G1, G2)" |
  "trace_collect_training_sets ((label, inputs, outputs)#t) uPTA s registers T1 T2 G1 G2 = (
    let
      (uids, s', tran) = fthe_elem (ffilter (\<lambda>(uids, s', tran). evaluate_outputs tran inputs registers = map Some outputs) (i_possible_steps uPTA s registers label inputs));
      updated = (evaluate_updates tran inputs registers)
    in
    if hd uids \<in> set T1 then
      trace_collect_training_sets t uPTA s' updated T1 T2 ((inputs, registers)#G1) G2
    else if hd uids \<in> set T2 then
      trace_collect_training_sets t uPTA s' updated T1 T2 G1 ((inputs, registers)#G2)
    else
      trace_collect_training_sets t uPTA s' updated T1 T2 G1 G2
  )"

primrec collect_training_sets :: "log \<Rightarrow> iEFSM \<Rightarrow> tids \<Rightarrow> tids \<Rightarrow> (inputs \<times> registers) list \<Rightarrow> (inputs \<times> registers) list \<Rightarrow> ((inputs \<times> registers) list \<times> (inputs \<times> registers) list)" where
  "collect_training_sets [] uPTA T1 T2 G1 G2 = (G1, G2)" |
  "collect_training_sets (h#t) uPTA T1 T2 G1 G2 = (
    let (G1a, G2a) = trace_collect_training_sets h uPTA 0 <> T1 T2 [] [] in
    collect_training_sets t uPTA T1 T2 (List.union G1 G1a) (List.union G2 G2a)
  )"

definition find_distinguishing_guards :: "(inputs \<times> registers) list \<Rightarrow> (inputs \<times> registers) list \<Rightarrow> (vname gexp \<times> vname gexp) option" where
  "find_distinguishing_guards G1 G2 = (
    let gs = {(g1, g2).
      (\<forall>(i, r) \<in> set G1. gval g1 (join_ir i r) = true) \<and>
      (\<forall>(i, r) \<in> set G2. gval g2 (join_ir i r) = true) \<and>
      (\<forall>i r. \<not> (gval g1 (join_ir i r) = true \<and> gval g2 (join_ir i r) = true))
    } in
    if gs = {} then None else Some (Eps (\<lambda>g. g \<in> gs))
  )"
declare find_distinguishing_guards_def [code del]
code_printing constant find_distinguishing_guards \<rightharpoonup> (Scala) "Dirties.findDistinguishingGuards"

definition add_guard :: "transition \<Rightarrow> vname gexp \<Rightarrow> transition" where
  "add_guard t g = t\<lparr>Guards := List.insert g (Guards t)\<rparr>"

definition distinguish :: "log \<Rightarrow> update_modifier" where
  "distinguish log t1ID t2ID s destMerge preDestMerge old check = (
    let
      t1 = get_by_ids destMerge t1ID;
      t2 = get_by_ids destMerge t2ID;
      uPTA = transfer_updates destMerge (make_pta log);
      (G1, G2) = collect_training_sets log uPTA t1ID t2ID [] []
    in
      case find_distinguishing_guards G1 G2 of
        None \<Rightarrow> None |
        Some (g1, g2) \<Rightarrow> (
          let rep = replace_transitions preDestMerge [(t1ID, add_guard t1 g1), (t2ID, add_guard t2 g2)] in
          if check (tm rep) then Some rep else None
        )
  )"

definition can_still_take_ctx :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> cfstate \<Rightarrow> cfstate \<Rightarrow> transition \<Rightarrow> transition \<Rightarrow> bool" where
  "can_still_take_ctx e1 e2 s1 s2 t1 t2 = (
    \<forall>t. recognises e1 t \<and> visits s1 e1 0 <> t \<and> recognises e2 t \<and> visits s2 e2 0 <> t \<longrightarrow>
    (\<forall>a. obtains s2 a e2 0 <> t  \<and> (\<forall>i. can_take_transition t2 i a \<longrightarrow> can_take_transition t1 i a))
  )"

lemma distinguishing_guard_subsumption:
"Label t1 = Label t2 \<Longrightarrow>
 Arity t1 = Arity t2 \<Longrightarrow>
 Outputs t1 = Outputs t2 \<Longrightarrow>
 Updates t1 = Updates t2 \<Longrightarrow>
 can_still_take_ctx e1 e2 s1 s2 t1 t2 \<Longrightarrow>
 recognises e1 p \<Longrightarrow>
 visits s1 e1 0 <> p \<Longrightarrow>
 obtains s2 c e2 0 <> p \<Longrightarrow>
 subsumes t1 c t2"
  apply (simp add: subsumes_def can_still_take_ctx_def)
  apply (erule_tac x=p in allE)
  apply simp
  by (simp add: obtains_recognises obtains_visits)

definition "recognises_and_visits_both a b s s' = (
  \<exists>p c1 c2. obtains s c1 a 0 <> p \<and> obtains s' c2 b 0 <> p)"

definition "can_still_take e1 e2 s1 s2 t1 t2 = (
  Label t1 = Label t2 \<and>
  Arity t1 = Arity t2 \<and>
  Outputs t1 = Outputs t2 \<and>
  Updates t1 = Updates t2 \<and>
  can_still_take_ctx e1 e2 s1 s2 t1 t2 \<and>
  recognises_and_visits_both e1 e2 s1 s2)"

lemma can_still_take_direct_subsumption:
  "can_still_take e1 e2 s1 s2 t1 t2 \<Longrightarrow>
  directly_subsumes e1 e2 s1 s2 t1 t2"
  apply (simp add: directly_subsumes_def can_still_take_def)
  apply standard
  by (meson distinguishing_guard_subsumption obtains_visits obtains_recognises recognises_and_visits_both_def)

end
