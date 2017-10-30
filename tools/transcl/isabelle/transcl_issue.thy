(******************************************************************************)
(* External Algorithm for Calculating the Transitive Closure in Isabelle/HOL  *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(* Email: frank.zeyda@york.ac.uk                                              *)
(******************************************************************************)

section {* Efficiency Issue *}

theory transcl_issue
imports transcl "~~/src/HOL/Library/Code_Target_Numeral"
begin

subsection {* Comparison with a priori @{method eval} *}

text \<open>Let us define a graph with 80 edges.\<close>

definition myrel :: "nat rel" where
"myrel = {
( 1,  2), ( 2,  3), ( 3,  4), ( 4,  5), ( 5,  6), ( 6,  7), ( 7,  8), ( 8,  9),
(11, 12), (12, 13), (13, 14), (14, 15), (15, 16), (16, 17), (17, 18), (18, 19),
(21, 22), (22, 23), (23, 24), (24, 25), (25, 26), (26, 27), (27, 28), (28, 29),
(31, 32), (32, 33), (33, 34), (34, 35), (35, 36), (36, 37), (37, 38), (38, 39),
(41, 42), (42, 43), (43, 44), (44, 45), (45, 46), (46, 47), (47, 48), (48, 49),
(51, 52), (52, 53), (53, 54), (54, 55), (55, 56), (56, 57), (57, 58), (58, 59),
(61, 62), (62, 63), (63, 64), (64, 65), (65, 66), (66, 67), (67, 68), (68, 69),
(71, 72), (72, 73), (73, 74), (74, 75), (75, 76), (76, 77), (77, 78), (78, 79),
(81, 82), (82, 83), (83, 84), (84, 85), (85, 86), (86, 87), (87, 88), (88, 89),
(91, 92), (92, 93), (93, 94), (94, 95), (95, 96), (96, 97), (97, 98), (98, 99)}"

definition myrel_tc:
"myrel_tc = transcl(myrel)"

text \<open>The following actually performs fairly efficient (about 1s).\<close>

lemma "acyclic myrel"
(* apply (code_simp) *)
apply (eval)
done

text \<open>That is because it directly invokes the SML code below.\<close>

export_code acyclic in SML

text \<open>We trade the above for a supposedly more efficient program.\<close>

export_code acyclic_witness in SML

text \<open>The price to pay is defining and exporting code for @{const myrel_tc}.\<close>

export_code myrel_tc in SML

lemma "acyclic myrel"
apply (rule acyclic_witnessI)
apply (rule_tac x = "transcl(myrel)" in exI)
apply (eval)
done

text \<open>
  It turns out that the algorithm is overall still slightly slower than using
  the @{method eval} method a priori on @{term "acyclic R"}. I wonder if there
  could be an efficiency gain when we operate on larger relations. I believe
  the primary reason for the algorithmic solution being slower is related to
  parsing and perhaps the code generation of the closure term. Using the HOL
  theory \<open>Code_Target_Numeral\<close> improves matters reasonably. Perhaps we have
  to consider further tricks and tweaks to speed up code generation. I guess
  that symbolic evaluation (via @{method simp}) is not giving us any reward.
\<close>

subsection {* Symbolic Evaluation *}

text \<open>Let us check whether we can proof the proviso by simplification.\<close>

text \<open>Additional simplification laws for proving @{term "acyclic_witness R"}.\<close>

lemma empty_subset:
"({} \<subseteq> A) = True"
apply (simp)
done

lemma irrefl_empty:
"irrefl {} = True"
apply (unfold irrefl_def)
apply (clarsimp)
done

lemma irrefl_insert:
"irrefl (insert (x, y) r) = ((x \<noteq> y) \<and> irrefl r)"
apply (unfold irrefl_def)
apply (clarsimp)
apply (blast)
done

lemmas relcomp_empty =
  relcomp_empty1
  relcomp_empty2

lemma relcomp_insert:
"(insert (a, b) R) O (insert (c, d) S) =
  (if b = c then {(a, d)} else {}) \<union>
    ((insert (a, b) R) O S) \<union> (R O (insert (c, d) S))"
apply (auto)
done

text \<open>Relevant laws for simplifying equalities on @{type nat} values.\<close>

lemmas nat_eq_simps =
  Num.eq_numeral_simps
  Num.pred_numeral_simps
  Num.num.distinct
  Num.num.inject
  Num.eq_numeral_Suc
  Num.Suc_eq_numeral
  Nat.nat.distinct
  Nat.nat.inject
  Nat.One_nat_def

text \<open>Relevant laws to simplify subset and membership expressions.\<close>

lemmas mem_subset_simps =
  insert_iff empty_iff insert_subset empty_subset HOL.simp_thms

text \<open>Unfortunately, simplification proofs are not as efficiently as I hoped.\<close>

text \<open>Irreflexivity is not too bad...\<close>

lemma "irrefl transcl(myrel)"
apply (unfold irrefl_insert irrefl_empty)
apply (simp only: nat_eq_simps simp_thms)
oops

text \<open>
  But subset proofs already become perceivably slower. We could perhaps make
  them faster again by letting the algorithm produce a relation whose initial
  maplets precisely correspond to that of the input relation.
\<close>

lemma "myrel \<subseteq> transcl(myrel)"
apply (unfold myrel_def)
apply (simp only: mem_subset_simps nat_eq_simps)
oops

-- \<open>It gets really tricky when trying to prove the closure property.\<close>

lemma "myrel_tc O myrel \<subseteq> myrel_tc"
apply (unfold myrel_def myrel_tc)
-- \<open>Due to the size of the relation, @{method eval} seems to struggle too...\<close>
(* apply (eval) *)
-- \<open>But the below is much much slower, and in fact not practical...\<close>
(* apply (simp only: mem_subset_simps relcomp_insert relcomp_empty nat_eq_simps) *)
oops

text \<open>
  In conclusion, simplification to discharge the proviso might be difficult,
  unless we devise and implement a clever way to do it! Code evaluation may
  actually be the best method, despite having to trust the evaluator.
\<close>

subsection {* Evaluation Experiments *}

value "acyclic {(a, b), (c, d), (e, f), (g, h)}"
value "{(a, b), (c, d)} \<subseteq> {(e, f), (g, h), (i, j)}"
value "({a, b} O {c, d}) \<subseteq> {e, f}"

text \<open>
  Note that slow-down is also down to an expansion of numbers into chained
  applications of @{const Suc}. This can be alleviated by changing the way
  numbers are translated into code include the theory \<open>Code_Target_Numberal\<close>
  from the HOL library. The effort here btw is not generating the code but
  translating it back into a HOL term.
\<close>

value myrel

text \<open>
  The difference in efficiency between the two evaluations below is explained
  through the effort of encoding @{const myrel_tc} before the code evaluation
  can be executed. (There is no effort in translating the result back here.)
  The question is whether the efficiency gained by executing our external C++
  algorithm dominates the efficiency lost by having to encode @{const myrel_tc}
  rather than @{const myrel}. I suppose this will be the case for relations
  larger than a certain size, but those might in any case be too big in order
  to process within Isabelle... :-(. The only thing we could do is to somewhat
  try and reduce the effort in code translation of large relations. Perhaps
  the problem is less pronounced if we used strings rather than numbers.
\<close>

value "irrefl (ntrancl 100 myrel)"
value "irrefl transcl(myrel)"

text \<open>
  Another pitfall to look out for is to avoid large expanded terms in favour
  of encapsulating them into local variables via `\<open>let x = _ in _\<close>' or global
  constants. This makes the code translation more efficient as a side-effect,
  approximately by a factor of 1.5 below.
\<close>

value "myrel_tc O myrel \<subseteq> myrel_tc"

value "transcl(myrel) O myrel \<subseteq> transcl(myrel)"

text \<open>
  Let us try to customise code generation to discharge the closure proviso.
\<close>

definition cl_proviso :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> bool" where
[code del]: "cl_proviso C R = (C O R \<subseteq> C)"

lemma cl_proviso_set [code]:
"cl_proviso C (set []) = True"
"cl_proviso C (set [y]) = (\<forall>x\<in>C. (snd x) = (fst y) \<longrightarrow> (fst x, snd y) \<in> C)"
"cl_proviso C (set (x # y # t)) =
  (cl_proviso C (set [x]) \<and> cl_proviso C (set (y # t)))"
apply (unfold cl_proviso_def)
apply (fastforce)+
done

export_code cl_proviso in SML

text \<open>In terms of speed, there is, however, no discernible difference.\<close>

value "cl_proviso myrel_tc myrel"
value "myrel_tc O myrel \<subseteq> myrel_tc"

lemma "cl_proviso transcl(myrel) myrel"
apply (eval)
oops

lemma "myrel_tc O myrel \<subseteq> myrel_tc"
apply (eval)
oops

subsection {* Conclusion *}

text \<open>
  The investigation revealed that the approach using an external algorithm and
  certifying the result might not universally faster than an immediate attack
  on @{term "acyclic R"} with the @{method eval} method. The reason is that we
  need cannot discharge the proviso @{const acyclic_witness} of the respective
  theorem @{thm [source] acyclic_witnessI} efficiently by simplification, and
  evaluation likewise incurs an overhead of encoding the (larger) relation that
  is to be certified. Direct proof of @{term "acyclic R"}, on the other hand,
  profits from a smaller relation to encode as part of code generation, and I
  presume for the external algorithm to dominate the naive one carried out by
  @{const acyclic} using @{const ntrancl} we need to consider much larger sets
  whose processing in Isabelle will already pose challenges.
\<close>

text \<open>
  All this is a bit disheartening, bearing in mind the effort that went into
  developing the tool chain. I still believe that for larger relations, it is
  faster than plain @{method eval} but this requires some more investigation.
  If time, it would be interesting to see if code generation of larger sets
  can somewhat be improved. Alternatively, one could write a (more) efficient
  algorithm for the transitive closure in ML and verify it in Isabelle/HOL.
  Lastly, the perhaps the C++ tool could be invoked after code generation has
  taken place. In that case, \<open>transcl(_)\<close> will actually be a function whose
  sole purpose is to be expanded during code generation (it does not have a
  HOL semantics). This might solve the efficiency trade-off (point 2 below).

  The two bottle-necks seem to be
    1. Declaring and Processing constants of large relations \<open>R\<close> and \<open>C\<close>.
    2. Code generation that discharges the proviso @{term "acyclic_witness C"}.

  The bottle-neck is not executing the algorithm per se --- this, at least,
  seems indeed to take place very efficiently. A side issue is whether the
  @{method eval} tactic results in a trusted proof. The link

  \url{https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2013-September/msg00014.html}

  to the Isabelle mailing list seems quite instructive. There seem to be three
  tactics: @{method code_simp}, @{method normalization}, and @{method eval}.
  The first one is fully trusted, the second and third one are not, using code
  evaluation and execution as an oracle.
\<close>
end