subsection\<open>Weak Subsumption\<close>
text\<open>Unfortunately, the \emph{direct subsumption} relation cannot be transformed into executable
code. To solve this problem, \cite{foster2019} advocates for the use of a model checker, but this
turns out to be prohibitively slow for all but the smallest of examples. To solve this problem, we
must make a practical compromise and use another heuristic: the \emph{weak subsumption} heuristic.
This heuristic simply tries to delete each transition in turn and runs the original traces used to
build the PTA are still accepted. If so, this is taken as an acceptable substitute for direct
subsumption.

The acceptability of this, with respect to model behaviour, is justified by the fact that the
original traces are checked for acceptance. In situations where one transition genuinely does
directly subsume the other, the merge will go ahead as normal. In situations where one transition
does not directly subsume the other, the merge may still go ahead if replacing one transition with
the other still allows the model to accept the original traces. In this case, the heuristic makes an
overgeneralisation, but this is deemed to be acceptable since this is what heuristics are for. This
approach is clearly not as formal as we would like, but the compromise is necessary to allow models
to be inferred in reasonable time.\<close>

theory Weak_Subsumption
imports "../Inference"
begin

definition maxBy :: "('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "maxBy f a b = (if (f a > f b) then a else b)"

fun weak_subsumption :: "update_modifier" where
  "weak_subsumption t1ID t2ID s new _ old check = (let
     t1 = get_by_ids new t1ID;
     t2 = get_by_ids new t2ID
     in
     if
      same_structure t1 t2
     then
      let
        maxT = maxBy (\<lambda>x. ((length \<circ> Updates) x, map snd (Updates x))) t1 t2;
        minT = if maxT = t1 then t2 else t1;
        newEFSMmax = replace_all new [t1ID, t2ID] maxT in
      \<comment> \<open>Most of the time, we'll want the transition with the most updates so start with that one\<close>
      if check (tm newEFSMmax) then
        Some newEFSMmax
      else
        \<comment> \<open>There may be other occasions where we want to try the other transition\<close>
        \<comment> \<open>e.g. if their updates are equal but one has a different guard\<close>
        let newEFSMmin = replace_all new [t1ID, t2ID] minT in
        if check (tm newEFSMmin) then
          Some newEFSMmin
        else
          None
     else
      None
   )"

end
