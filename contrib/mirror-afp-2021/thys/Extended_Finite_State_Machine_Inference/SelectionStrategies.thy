section\<open>Selection Strategies\<close>
text\<open>The strategy used to idenfity and prioritise states to be merged plays a big part in how the
final model turns out. This theory file presents a number of different selection strategies.\<close>

theory SelectionStrategies
imports Inference
begin

(* One point if they're equal *)
text\<open>The simplest strategy is to assign one point for each shared pair of transitions.\<close>
definition exactly_equal :: strategy where
  "exactly_equal t1ID t2ID e = bool2nat ((get_by_ids e t1ID) = (get_by_ids e t2ID))"

text\<open>Another simple strategy is to look at the labels and arities of outgoing transitions of each
state. Pairs of states are ranked by how many transitions with the same label and arity they have in
common.\<close>
definition naive_score :: strategy where
  "naive_score t1ID t2ID e = (
  let
    t1 = get_by_ids e t1ID;
    t2 = get_by_ids e t2ID
  in
  bool2nat (Label t1 = Label t2 \<and> Arity t1 = Arity t2 \<and> length (Outputs t1) = length (Outputs t2))
)"

text\<open>Building off the above strategy, it makes sense to give transitions an extra ``bonus point'' if
they are exactly equal.\<close>
definition naive_score_eq_bonus :: strategy where
  "naive_score_eq_bonus t1ID t2ID e = (
  let
    t1 = get_by_ids e t1ID;
    t2 = get_by_ids e t2ID
  in
  score_transitions t1 t2
)"

(* One point each for equal label, arity, and outputs *)
text\<open>Another strategy is to assign bonus points for each shared output.\<close>
definition naive_score_outputs :: strategy where
  "naive_score_outputs t1ID t2ID e = (
  let
    t1 = get_by_ids e t1ID;
    t2 = get_by_ids e t2ID
  in
    bool2nat (Label t1 = Label t2) + bool2nat (Arity t1 = Arity t2) + bool2nat (Outputs t1 = Outputs t2)
)"

(* Functions with same label, and input and output arities contribute one point for each guard    *)
(* and output they share. *)
text\<open>Along similar lines, we can assign additional bonus points for shared guards.\<close>
definition naive_score_comprehensive :: strategy where
  "naive_score_comprehensive t1ID t2ID e = (
  let
    t1 = get_by_ids e t1ID;
    t2 = get_by_ids e t2ID
  in
  if Label t1 = Label t2 \<and> Arity t1 = Arity t2 then
    if length (Outputs t1) = length (Outputs t2) then
      card (set (Guards t1) \<inter> set (Guards t2)) + length (filter (\<lambda>(p1, p2). p1 = p2) (zip (Outputs t1) (Outputs t2)))
    else 0
  else 0
)"

(* Functions with same label, and input and output arities contribute one point for each guard    *)
(* and output they share. Transitions which are exactly equal get a very high score. *)
text\<open>This strategy is similar to the one above except that transitions which are exactly equal get
100 bonus points. \<close>
definition naive_score_comprehensive_eq_high :: strategy where
  "naive_score_comprehensive_eq_high t1ID t2ID e = (
  let
    t1 = get_by_ids e t1ID;
    t2 = get_by_ids e t2ID
  in
  if t1 = t2 then
    100
  else
    if Label t1 = Label t2 \<and> Arity t1 = Arity t2 then
      if length (Outputs t1) = length (Outputs t2) then
        card (set (Guards t1) \<inter> set (Guards t2)) + length (filter (\<lambda>(p1, p2). p1 = p2) (zip (Outputs t1) (Outputs t2)))
      else 0
    else 0
)"

(* One point if one subsumes the other *)
text\<open>We can incorporate the subsumption relation into the scoring of merges such that a pair of
states receives one point for each pair of transitions where one directly subsumes the other.\<close>
definition naive_score_subsumption :: "strategy" where
  "naive_score_subsumption t1ID t2ID e = (
  let
    t1 = get_by_ids e t1ID;
    t2 = get_by_ids e t2ID;
    s = origin t1ID e
  in
  bool2nat (directly_subsumes (tm e) (tm e) s s t1 t2) + bool2nat (directly_subsumes (tm e) (tm e) s s t2 t1)
)"

(* Orders by the origin state so we merge leaves first *)
text\<open>An alternative strategy is to simply score merges based on the states' proximity to the origin.\<close>
definition leaves :: strategy where
  "leaves t1ID t2ID e = (
    let
      t1 = get_by_ids e t1ID;
      t2 = get_by_ids e t2ID
    in
    if (Label t1 = Label t2 \<and> Arity t1 = Arity t2 \<and> length (Outputs t1) = length (Outputs t2)) then
      origin t1ID e + origin t2ID e
    else
      0)"

end
